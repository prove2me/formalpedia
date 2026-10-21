-- Prove2me | solution 1 for SherbrookeMetric.ConvexHull.marginal_unique
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:51:57.057136+00:00
-- url     : https://prove2.me/submissions/52430a4c-8d37-45cc-b516-ded51fd862a6

import Mathlib
import Definitions.Def_SherbrookeMetric_ConvexHull_LowerHull
import Definitions.Def_SherbrookeMetric_ConvexHull_MarginalConditions

set_option autoImplicit false
open SherbrookeMetric.ConvexHull ServiceParts.StockLevels

namespace SMCAux

lemma fdiff2_eq (f : ℕ → ℝ) (m : ℕ) :
    fdiff2 f m = f (m + 2) - 2 * f (m + 1) + f m := by
  unfold fdiff2 fdiff
  have : m + 1 + 1 = m + 2 := rfl
  rw [this]; ring

lemma fdiff_mono {g : ℕ → ℝ} (hg : DiscreteConvex g) : Monotone (fdiff g) :=
  monotone_nat_of_le_succ (fun m => by
    have := hg m
    unfold fdiff2 at this
    linarith)

lemma fdiff_nonpos_of_bdd {g : ℕ → ℝ} (hg : DiscreteConvex g) {C : ℝ}
    (hC : ∀ m, g m ≤ C) (m : ℕ) : fdiff g m ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  have hmono := fdiff_mono hg
  have key : ∀ n : ℕ, g m + n * fdiff g m ≤ g (m + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : fdiff g m ≤ fdiff g (m + n) := hmono (by omega)
      have h2 : g (m + n + 1) = g (m + n) + fdiff g (m + n) := by unfold fdiff; ring
      have : m + (n + 1) = m + n + 1 := by omega
      rw [this, h2]; push_cast; linarith
  obtain ⟨n, hn⟩ := Archimedean.arch (C - g m + 1) hpos
  have := key n
  have := hC (m + n)
  simp only [nsmul_eq_mul] at hn
  linarith

lemma exists_lb {Ξ : ℕ → ℝ} (hbdd : BddBelow (Set.range Ξ)) : ∃ b : ℝ, ∀ k, b ≤ Ξ k := by
  obtain ⟨b, hb⟩ := hbdd
  exact ⟨b, fun k => hb (Set.mem_range_self k)⟩

lemma const_convex (b : ℝ) : DiscreteConvex (fun _ : ℕ => b) := by
  intro m; simp [fdiff2, fdiff]

lemma fam_nonempty {Ξ : ℕ → ℝ} (hbdd : BddBelow (Set.range Ξ)) :
    Nonempty {g : ℕ → ℝ // DiscreteConvex g ∧ ∀ k : ℕ, g k ≤ Ξ k} := by
  obtain ⟨b, hb⟩ := exists_lb hbdd
  exact ⟨⟨fun _ => b, const_convex b, hb⟩⟩

lemma le_hull {Ξ : ℕ → ℝ} {g : ℕ → ℝ} (hg : DiscreteConvex g) (hle : ∀ k, g k ≤ Ξ k) (m : ℕ) :
    g m ≤ lowerHull Ξ m := by
  unfold lowerHull
  refine le_ciSup (f := fun g : {g : ℕ → ℝ // DiscreteConvex g ∧ ∀ k : ℕ, g k ≤ Ξ k} => g.1 m)
    ⟨Ξ m, ?_⟩ ⟨g, hg, hle⟩
  rintro _ ⟨g', rfl⟩
  exact g'.2.2 m

lemma hull_le {Ξ : ℕ → ℝ} (hbdd : BddBelow (Set.range Ξ)) (m : ℕ) : lowerHull Ξ m ≤ Ξ m := by
  haveI := fam_nonempty hbdd
  exact ciSup_le (fun g => g.2.2 m)

lemma hull_convex {Ξ : ℕ → ℝ} (hbdd : BddBelow (Set.range Ξ)) : DiscreteConvex (lowerHull Ξ) := by
  haveI := fam_nonempty hbdd
  intro m
  rw [fdiff2_eq]
  have : lowerHull Ξ (m + 1) ≤ (lowerHull Ξ m + lowerHull Ξ (m + 2)) / 2 := by
    refine ciSup_le (fun g => ?_)
    have h1 := g.2.1 m
    rw [fdiff2_eq] at h1
    have h2 : g.1 m ≤ lowerHull Ξ m := le_hull g.2.1 g.2.2 m
    have h3 : g.1 (m + 2) ≤ lowerHull Ξ (m + 2) := le_hull g.2.1 g.2.2 (m + 2)
    linarith
  linarith

lemma hull_lb {Ξ : ℕ → ℝ} {b : ℝ} (hb : ∀ k, b ≤ Ξ k) (m : ℕ) : b ≤ lowerHull Ξ m :=
  le_hull (const_convex b) hb m

lemma hull_fdiff_nonpos {Ξ : ℕ → ℝ} (hanti : Antitone Ξ) (hbdd : BddBelow (Set.range Ξ)) (m : ℕ) :
    fdiff (lowerHull Ξ) m ≤ 0 :=
  fdiff_nonpos_of_bdd (hull_convex hbdd) (C := Ξ 0)
    (fun k => (hull_le hbdd k).trans (hanti (Nat.zero_le k))) m

lemma hull_tendsto {Ξ : ℕ → ℝ} (hanti : Antitone Ξ) (hbdd : BddBelow (Set.range Ξ)) :
    Filter.Tendsto (fdiff (lowerHull Ξ)) Filter.atTop (nhds 0) := by
  obtain ⟨b, hb⟩ := exists_lb hbdd
  have hmono := fdiff_mono (hull_convex hbdd)
  have hnp := hull_fdiff_nonpos hanti hbdd
  have hlb := hull_lb hb
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- some N with fdiff H N > -ε
  have : ∃ N, -ε < fdiff (lowerHull Ξ) N := by
    by_contra hcon
    push_neg at hcon
    have key : ∀ n : ℕ, lowerHull Ξ 0 - n * ε ≥ lowerHull Ξ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have := hcon n
        have h2 : lowerHull Ξ (n + 1) = lowerHull Ξ n + fdiff (lowerHull Ξ) n := by unfold fdiff; ring
        rw [h2]; push_cast; linarith
    obtain ⟨n, hn⟩ := Archimedean.arch (lowerHull Ξ 0 - b + 1) hε
    simp only [nsmul_eq_mul] at hn
    have := key n
    have := hlb n
    linarith
  obtain ⟨N, hN⟩ := this
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hmono hn
  have h2 := hnp n
  rw [Real.dist_eq, sub_zero, abs_lt]
  constructor <;> linarith


lemma slopes_antitone {Ξ : ℕ → ℝ} (hanti : Antitone Ξ) (hbdd : BddBelow (Set.range Ξ)) :
    Antitone (lowerHull Ξ) :=
  antitone_nat_of_succ_le (fun m => by
    have := hull_fdiff_nonpos hanti hbdd m
    unfold fdiff at this
    linarith)

lemma exists_aux {Ξ : ℕ → ℝ} (c : ℝ) (hc : 0 < c) (hanti : Antitone Ξ)
    (hbdd : BddBelow (Set.range Ξ)) : ∃ m : ℕ, MarginalConditions c (lowerHull Ξ) m := by
  classical
  have hev := (hull_tendsto hanti hbdd).eventually (lt_mem_nhds (show -c < 0 by linarith))
  obtain ⟨N, hN⟩ := hev.exists
  have hex : ∃ m, 0 ≤ c + fdiff (lowerHull Ξ) m := ⟨N, by linarith⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, fun k hk => ?_⟩
  have := Nat.find_min hex (show k < Nat.find hex by omega)
  push_neg at this
  exact this

lemma not_lt_aux {H : ℕ → ℝ} (hH : DiscreteConvex H) (c : ℝ) (m n : ℕ)
    (hm : MarginalConditions c H m) (hn : MarginalConditions c H n) : ¬ m < n := by
  intro h
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 := hn.2 k rfl
  have h2 := fdiff_mono hH (show m ≤ k by omega)
  have h3 := hm.1
  linarith

lemma unique_aux {H : ℕ → ℝ} (hH : DiscreteConvex H) (c : ℝ) (m n : ℕ)
    (hm : MarginalConditions c H m) (hn : MarginalConditions c H n) : m = n :=
  le_antisymm (not_lt.mp (not_lt_aux hH c n m hn hm)) (not_lt.mp (not_lt_aux hH c m n hm hn))

lemma optimal_aux {H : ℕ → ℝ} (hH : DiscreteConvex H) (c : ℝ) (mbar : ℕ)
    (hmc : MarginalConditions c H mbar) (m : ℕ) :
    c * (mbar : ℝ) + H mbar ≤ c * (m : ℝ) + H m := by
  have hmono := fdiff_mono hH
  rcases le_total mbar m with h | h
  · induction m, h using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih =>
      have h1 := hmono hn
      have h2 := hmc.1
      have h3 : H (n + 1) = H n + fdiff H n := by unfold fdiff; ring
      rw [h3]; push_cast; linarith
  · have key : ∀ d m : ℕ, m + d = mbar → c * (mbar : ℝ) + H mbar ≤ c * (m : ℝ) + H m := by
      intro d
      induction d with
      | zero => intro m hm; simp at hm; subst hm; exact le_rfl
      | succ d ih =>
        intro m hm
        have h1 := ih (m + 1) (by omega)
        have h2 := hmc.2 (m + d) (by omega)
        have h3 := hmono (show m ≤ m + d by omega)
        have h4 : H (m + 1) = H m + fdiff H m := by unfold fdiff; ring
        rw [h4] at h1; push_cast at h1; linarith
    exact key (mbar - m) m (by omega)

lemma contact_aux {Ξ : ℕ → ℝ} (c : ℝ) (hanti : Antitone Ξ)
    (hbdd : BddBelow (Set.range Ξ)) (mbar : ℕ) (hmc : MarginalConditions c (lowerHull Ξ) mbar) :
    lowerHull Ξ mbar = Ξ mbar := by
  have hle := hull_le hbdd mbar
  by_contra hne
  have hlt : lowerHull Ξ mbar < Ξ mbar := lt_of_le_of_ne hle hne
  obtain ⟨δ, hδpos, hδle, hδslack⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ Ξ mbar - lowerHull Ξ mbar ∧
      (∀ k, mbar = k + 1 → 2 * δ ≤ fdiff2 (lowerHull Ξ) k) := by
    cases mbar with
    | zero => exact ⟨Ξ 0 - lowerHull Ξ 0, by linarith, le_rfl, fun k hk => absurd hk (by omega)⟩
    | succ k0 =>
      have h1 := hmc.1
      have h2 := hmc.2 k0 rfl
      have hs : 0 < fdiff2 (lowerHull Ξ) k0 := by unfold fdiff2; linarith
      refine ⟨min (Ξ (k0 + 1) - lowerHull Ξ (k0 + 1)) (fdiff2 (lowerHull Ξ) k0 / 2),
        lt_min (by linarith) (by linarith), min_le_left _ _, fun k hk => ?_⟩
      have : k = k0 := by omega
      subst this
      have := min_le_right (Ξ (k + 1) - lowerHull Ξ (k + 1)) (fdiff2 (lowerHull Ξ) k / 2)
      linarith
  have hHc : DiscreteConvex (lowerHull Ξ) := hull_convex hbdd
  have hconv : DiscreteConvex (fun n => lowerHull Ξ n + if n = mbar then δ else 0) := by
    intro m
    rw [fdiff2_eq]
    have hH := hHc m
    rw [fdiff2_eq] at hH
    have hs : m + 1 = mbar → 2 * δ ≤ lowerHull Ξ (m + 2) - 2 * lowerHull Ξ (m + 1) + lowerHull Ξ m := fun h => by
      have := hδslack m h.symm
      rwa [fdiff2_eq] at this
    by_cases h0 : m = mbar
    · have e1 : ¬ (m + 1 = mbar) := by omega
      have e2 : ¬ (m + 2 = mbar) := by omega
      simp only [if_pos h0, if_neg e1, if_neg e2]; linarith
    · by_cases h1 : m + 1 = mbar
      · have e2 : ¬ (m + 2 = mbar) := by omega
        have := hs h1
        simp only [if_neg h0, if_pos h1, if_neg e2]; linarith
      · by_cases h2 : m + 2 = mbar
        · simp only [if_neg h0, if_neg h1, if_pos h2]; linarith
        · simp only [if_neg h0, if_neg h1, if_neg h2]; linarith
  have hmin : ∀ n, (lowerHull Ξ n + if n = mbar then δ else 0) ≤ Ξ n := by
    intro n
    have := hull_le hbdd n
    by_cases h : n = mbar
    · subst h; rw [if_pos rfl]; linarith
    · simp only [if_neg h]; linarith
  have := le_hull hconv hmin mbar
  rw [if_pos rfl] at this
  linarith

end SMCAux

open SMCAux

theorem solution (Ξ : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hanti : Antitone Ξ) (hbdd : BddBelow (Set.range Ξ))
    (m n : ℕ) (hm : MarginalConditions c (lowerHull Ξ) m)
    (hn : MarginalConditions c (lowerHull Ξ) n) : m = n :=
  unique_aux (hull_convex hbdd) c m n hm hn
