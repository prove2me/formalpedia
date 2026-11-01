-- Prove2me | solution 1 for RapidRatePoisson.WeakConv.thinned_simple
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T10:54:44.313349+00:00
-- url     : https://prove2.me/submissions/f73d0e0f-c1eb-4a58-9b61-70e749fd38b9

import Mathlib
import Definitions.Def_RapidRatePoisson_WeakConv_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open RapidRatePoisson.WeakConv

namespace RRPThinnedSimple

/-- number of kept marks among `1, …, k`. -/
noncomputable def cnt {Ω : Type*} (β : ℕ → Ω → Bool) (ω : Ω) (k : ℕ) : ℕ :=
  ((Finset.Icc 1 k).filter fun i => β i ω = true).card

lemma cnt_zero {Ω : Type*} (β : ℕ → Ω → Bool) (ω : Ω) : cnt β ω 0 = 0 := by
  simp [cnt]

lemma cnt_mono {Ω : Type*} (β : ℕ → Ω → Bool) (ω : Ω) : Monotone (cnt β ω) := by
  intro a b hab
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.Icc_subset_Icc le_rfl hab

lemma cnt_succ_le {Ω : Type*} (β : ℕ → Ω → Bool) (ω : Ω) (k : ℕ) :
    cnt β ω (k + 1) ≤ cnt β ω k + 1 := by
  unfold cnt
  have : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [this, Finset.filter_insert]
  split_ifs
  · exact Finset.card_insert_le _ _
  · exact Nat.le_succ _

lemma thinned_eq {Ω : Type*} (N : ℝ≥0 → Ω → ℝ) (β : ℕ → Ω → Bool) (ε t : ℝ≥0) (ω : Ω) :
    thinned N β ε t ω = (cnt β ω ⌊N (t / ε) ω⌋₊ : ℝ) := rfl

lemma floor_eq_of_nat {x : ℝ} {m : ℕ} (h : x = m) : (⌊x⌋₊ : ℝ) = x := by
  rw [h, Nat.floor_natCast]

end RRPThinnedSimple

open RRPThinnedSimple in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (N : ℝ≥0 → Ω → ℝ)
    (β : ℕ → Ω → Bool) (ε : ℝ≥0) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ ω, MartingaleHT.InfiniteServer.IsUnitJumpCountingPath (fun t => N t ω) →
      MartingaleHT.InfiniteServer.IsUnitJumpCountingPath (fun t => thinned N β ε t ω)) ∧
    ((∀ t, Measurable (N t)) → (∀ i, 1 ≤ i → Measurable (β i)) →
      ∀ t, Measurable (thinned N β ε t)) := by
  -- the time change `s ↦ s / ε`
  have hcont : Continuous fun s : ℝ≥0 => s / ε := by
    simp_rw [div_eq_mul_inv]; exact continuous_id.mul continuous_const
  have hsmono : StrictMono fun s : ℝ≥0 => s / ε := by
    intro a b hab; exact div_lt_div_of_pos_right hab hε
  refine ⟨?_, ?_⟩
  · intro ω hNω
    obtain ⟨h0, hnat, hmono, hrc, hjump⟩ := hNω
    -- N(s) equals its floor
    have hfl : ∀ s, ((⌊N s ω⌋₊ : ℕ) : ℝ) = N s ω := by
      intro s; obtain ⟨m, hm⟩ := hnat s; exact floor_eq_of_nat hm
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [thinned_eq, h0, cnt_zero]
    · intro t; exact ⟨_, thinned_eq N β ε t ω⟩
    · intro a b hab
      simp only [thinned_eq]
      exact_mod_cast cnt_mono β ω (Nat.floor_le_floor (hmono (div_le_div_of_nonneg_right hab
        (le_of_lt hε))))
    · intro t
      -- eventually the floor is constant to the right of t
      have hT : Tendsto (fun s : ℝ≥0 => s / ε) (𝓝[≥] t) (𝓝[≥] (t / ε)) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · exact (hcont.tendsto t).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with s hs
          exact div_le_div_of_nonneg_right hs (le_of_lt hε)
      have hc : Tendsto (fun s => N (s / ε) ω) (𝓝[≥] t) (𝓝 (N (t / ε) ω)) :=
        (hrc (t / ε)).tendsto.comp hT
      have hev : ∀ᶠ s in 𝓝[≥] t, N (s / ε) ω < N (t / ε) ω + 1 :=
        hc.eventually (gt_mem_nhds (by linarith))
      have hev2 : ∀ᶠ s in 𝓝[≥] t, ⌊N (s / ε) ω⌋₊ = ⌊N (t / ε) ω⌋₊ := by
        filter_upwards [hev, self_mem_nhdsWithin] with s hs hst
        have hle : N (t / ε) ω ≤ N (s / ε) ω :=
          hmono (div_le_div_of_nonneg_right hst (le_of_lt hε))
        have a1 := hfl (s / ε); have a2 := hfl (t / ε)
        have : (⌊N (s / ε) ω⌋₊ : ℝ) < ⌊N (t / ε) ω⌋₊ + 1 := by linarith
        have : (⌊N (t / ε) ω⌋₊ : ℝ) ≤ ⌊N (s / ε) ω⌋₊ := by linarith
        have h1' : (⌊N (s / ε) ω⌋₊ : ℝ) < ⌊N (t / ε) ω⌋₊ + 1 := by linarith
        have h1 : ⌊N (s / ε) ω⌋₊ < ⌊N (t / ε) ω⌋₊ + 1 := by exact_mod_cast h1'
        have h2 : ⌊N (t / ε) ω⌋₊ ≤ ⌊N (s / ε) ω⌋₊ := by exact_mod_cast this
        omega
      apply tendsto_const_nhds.congr'
      filter_upwards [hev2] with s hs
      simp only [thinned_eq, hs]
    · intro t ht
      have htε : 0 < t / ε := div_pos ht hε
      have hT : Tendsto (fun s : ℝ≥0 => s / ε) (𝓝[<] t) (𝓝[<] (t / ε)) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · exact (hcont.tendsto t).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with s hs
          exact hsmono hs
      filter_upwards [hT.eventually (hjump (t / ε) htε), self_mem_nhdsWithin] with s hs hst
      simp only [thinned_eq]
      have hle : N (s / ε) ω ≤ N (t / ε) ω :=
        hmono (div_le_div_of_nonneg_right (le_of_lt hst) (le_of_lt hε))
      have a1 := hfl (s / ε); have a2 := hfl (t / ε)
      set a := ⌊N (s / ε) ω⌋₊
      set b := ⌊N (t / ε) ω⌋₊
      have hab : a ≤ b := by exact_mod_cast (show (a : ℝ) ≤ b by linarith)
      have hba : b ≤ a + 1 := by exact_mod_cast (show (b : ℝ) ≤ a + 1 by linarith)
      have hc : cnt β ω b ≤ cnt β ω a + 1 := by
        rcases Nat.eq_or_lt_of_le hab with h | h
        · rw [h]; omega
        · have : b = a + 1 := by omega
          rw [this]; exact cnt_succ_le β ω a
      have : (cnt β ω b : ℝ) ≤ cnt β ω a + 1 := by exact_mod_cast hc
      linarith
  · intro hNm hβm t
    have hg : ∀ k : ℕ, Measurable fun ω => (cnt β ω k : ℝ) := by
      intro k
      have : (fun ω => (cnt β ω k : ℝ)) =
          fun ω => ∑ i ∈ Finset.Icc 1 k, (if β i ω = true then (1 : ℝ) else 0) := by
        funext ω
        simp only [cnt, Finset.card_filter]
        push_cast
        rfl
      rw [this]
      apply Finset.measurable_sum
      intro i hi
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      apply Measurable.ite _ measurable_const measurable_const
      exact (hβm i hi1) (measurableSet_singleton true)
    have hF : Measurable fun p : Ω × ℕ => (cnt β p.1 p.2 : ℝ) :=
      measurable_from_prod_countable_left (fun k => hg k)
    have hn : Measurable fun ω => ⌊N (t / ε) ω⌋₊ := (hNm (t / ε)).nat_floor
    have heq : thinned N β ε t =
        (fun p : Ω × ℕ => (cnt β p.1 p.2 : ℝ)) ∘ (fun ω => (ω, ⌊N (t / ε) ω⌋₊)) := rfl
    rw [heq]
    exact hF.comp (measurable_id.prodMk hn)
