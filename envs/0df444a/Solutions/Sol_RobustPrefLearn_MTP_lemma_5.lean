-- Prove2me | solution 1 for RobustPrefLearn.MTP.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T14:57:04.651277+00:00
-- url     : https://prove2.me/submissions/a14b11c7-013a-4c67-9d98-66e53973dedd

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Mtp
import Theorems.Thm_RobustPrefLearn_MTP_lemma_6

open scoped ENNReal

namespace MTPAux10
open RobustPrefLearn.MTP

lemma rank_ge_one {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : DS K) (X : Fin K) (hX : X ∈ S.1) :
    1 ≤ relRank τ S X :=
  Finset.card_pos.2 ⟨X, Finset.mem_filter.2 ⟨hX, le_rfl⟩⟩

lemma rank_le_card {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : DS K) (X : Fin K) :
    relRank τ S X ≤ S.1.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

lemma rank_strict {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : DS K) (X X' : Fin K)
    (hX' : X' ∈ S.1) (hlt : τ X < τ X') : relRank τ S X < relRank τ S X' := by
  unfold relRank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨X', Finset.mem_filter.2 ⟨hX', le_rfl⟩, ?_⟩
    intro h
    exact absurd (Finset.mem_filter.1 h).2 (not_le.2 hlt)
  · intro k hk
    simp only [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, hk.2.trans hlt.le⟩

lemma rank_lt_iff {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : DS K) (X X' : Fin K)
    (hX : X ∈ S.1) (hX' : X' ∈ S.1) : relRank τ S X < relRank τ S X' ↔ τ X < τ X' := by
  constructor
  · intro h
    by_contra hc
    rcases (not_lt.1 hc).lt_or_eq with h' | h'
    · exact absurd (rank_strict τ S X' X hX h') (not_lt.2 h.le)
    · rw [τ.injective h'] at h; exact lt_irrefl _ h
  · exact rank_strict τ S X X' hX'

lemma rank_inj {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : DS K) (X X' : Fin K)
    (hX : X ∈ S.1) (hX' : X' ∈ S.1) (h : relRank τ S X = relRank τ S X') : X = X' := by
  by_contra hne
  rcases lt_or_gt_of_ne (fun e : τ X = τ X' => hne (τ.injective e)) with h1 | h1
  · exact absurd h (rank_strict τ S X X' hX' h1).ne
  · exact absurd h.symm (rank_strict τ S X' X hX h1).ne

/-- The rank map `S → Fin |S|`, `X ↦ τ(X|S) - 1`, is a bijection. -/
noncomputable def rankEquiv {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : DS K) : S.1 ≃ Fin S.1.card :=
  Equiv.ofBijective (fun x => ⟨relRank τ S x.1 - 1, by
      have := rank_le_card τ S x.1; have := rank_ge_one τ S x.1 x.2; omega⟩) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp⟩
    intro x y hxy
    simp only [Fin.mk.injEq] at hxy
    have := rank_ge_one τ S x.1 x.2; have := rank_ge_one τ S y.1 y.2
    exact Subtype.ext (rank_inj τ S x.1 y.1 x.2 y.2 (by omega)))

lemma rankEquiv_val {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : DS K) (x : S.1) :
    ((rankEquiv τ S x : Fin S.1.card) : ℕ) = relRank τ S x.1 - 1 := rfl

/-- Chain property of `p`-separability along consecutive ranks. -/
lemma psep_chain {K : ℕ} (p : ℝ) (hp0 : 0 < p) (f : Pref K) (σf : Equiv.Perm (Fin K))
    (hps : PSep p f σf) (hfnn : ∀ S X, 0 ≤ f S X) (S : DS K) :
    ∀ d : ℕ, ∀ i j : Fin K, i ∈ S.1 → j ∈ S.1 → relRank σf S i = relRank σf S j + d →
      f S i ≤ p ^ d * f S j := by
  intro d
  induction d with
  | zero =>
    intro i j hi hj h
    rw [rank_inj σf S i j hi hj (by simpa using h)]; simp
  | succ d ih =>
    intro i j hi hj h
    -- the element of rank `r(j) + d`
    have hlt : relRank σf S j + d - 1 < S.1.card := by
      have := rank_le_card σf S i; omega
    obtain ⟨m, hm⟩ := (rankEquiv σf S).surjective ⟨relRank σf S j + d - 1, hlt⟩
    have hmv := congrArg Fin.val hm
    rw [rankEquiv_val] at hmv
    simp only at hmv
    have hm1 := rank_ge_one σf S m.1 m.2
    have hj1 := rank_ge_one σf S j hj
    have hrm : relRank σf S m.1 = relRank σf S j + d := by omega
    have h1 : f S i ≤ p * f S m.1 :=
      hps S m.1 i m.2 hi ((rank_lt_iff σf S m.1 i m.2 hi).1 (by omega))
    have h2 := ih m.1 j m.2 hj hrm
    calc f S i ≤ p * f S m.1 := h1
      _ ≤ p * (p ^ d * f S j) := by gcongr
      _ = p ^ (d + 1) * f S j := by ring

/-- The supermartingale inequality: `∑_{X∈S} f(X|S) f^OA_σ(X|S)/f^OA_{σ_f}(X|S) ≤ 1`. -/
theorem ratio_sum_le_one {K : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (σf : Equiv.Perm (Fin K)) (hps : PSep p f σf)
    (σ : Equiv.Perm (Fin K)) (S : DS K) :
    ∑ X ∈ S.1, f S X * (oa p σ S X / oa p σf S X) ≤ 1 := by
  classical
  have hfnn : ∀ S X, 0 ≤ f S X := by
    intro S X
    by_cases hX : X ∈ S.1
    · exact ((hf.1 S X).1 hX).le
    · exact ((hf.1 S X).2 hX).ge
  set n := S.1.card
  have hc : 0 < (1 - p) / (1 - p ^ n) := by
    have : p ^ n < 1 := pow_lt_one₀ hp0.le hp1 (by have := S.2; omega)
    apply div_pos <;> linarith
  set rσ := fun X => relRank σ S X
  set rf := fun X => relRank σf S X
  have hratio : ∀ X ∈ S.1, oa p σ S X / oa p σf S X = p ^ (rσ X - 1) / p ^ (rf X - 1) := by
    intro X hX
    simp only [oa, if_pos hX, rσ, rf]
    rw [mul_div_mul_left _ _ hc.ne']
  -- move to the subtype
  let u : S.1 → ℝ := fun x => f S x.1 / p ^ (rf x.1 - 1)
  let w : S.1 → ℝ := fun x => p ^ (rf x.1 - 1)
  let π : Equiv.Perm S.1 := (rankEquiv σ S).trans (rankEquiv σf S).symm
  have hπ : ∀ x, rf (π x).1 = rσ x.1 := by
    intro x
    have h1 : rankEquiv σf S (π x) = rankEquiv σ S x := by simp [π]
    have h2 := congrArg Fin.val h1
    rw [rankEquiv_val, rankEquiv_val] at h2
    have := rank_ge_one σf S (π x).1 (π x).2
    have := rank_ge_one σ S x.1 x.2
    simp only [rf, rσ]; omega
  have hmono : Monovary u w := by
    intro i j hij
    simp only [w] at hij
    have hlt : rf j.1 - 1 < rf i.1 - 1 := (pow_lt_pow_iff_right_of_lt_one₀ hp0 hp1).1 hij
    have hi1 := rank_ge_one σf S i.1 i.2
    have hj1 := rank_ge_one σf S j.1 j.2
    have hch := psep_chain p hp0 f σf hps hfnn S (rf i.1 - rf j.1) i.1 j.1 i.2 j.2
      (by simp only [rf] at hlt ⊢; omega)
    simp only [u]
    rw [div_le_div_iff₀ (pow_pos hp0 _) (pow_pos hp0 _)]
    have e : rf i.1 - 1 = (rf j.1 - 1) + (rf i.1 - rf j.1) := by simp only [rf] at hlt ⊢; omega
    rw [e, pow_add]
    calc f S i.1 * p ^ (rf j.1 - 1) ≤ p ^ (rf i.1 - rf j.1) * f S j.1 * p ^ (rf j.1 - 1) := by
          gcongr
      _ = f S j.1 * (p ^ (rf j.1 - 1) * p ^ (rf i.1 - rf j.1)) := by ring
  have hre := hmono.sum_mul_comp_perm_le_sum_mul (σ := π)
  have hsum1 : ∑ x : S.1, u x * w x = 1 := by
    have : ∀ x : S.1, u x * w x = f S x.1 := by
      intro x; simp only [u, w]; field_simp
    simp_rw [this]
    rw [Finset.sum_coe_sort S.1 (fun X => f S X)]
    exact hf.2.1 S
  have hsum2 : ∑ x : S.1, u x * w (π x) = ∑ X ∈ S.1, f S X * (oa p σ S X / oa p σf S X) := by
    rw [← Finset.sum_coe_sort S.1]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [u, w, hπ x]
    rw [hratio x.1 x.2]
    ring
  rw [← hsum2, ← hsum1]
  exact hre

end MTPAux10

namespace MTPAux7
open RobustPrefLearn.MTP

lemma sum_rank {K : ℕ} (g : ℕ → ℝ) (T : Finset (Fin K)) :
    ∑ X ∈ T, g (T.filter (fun k => k ≤ X)).card = ∑ j ∈ Finset.range T.card, g (j + 1) := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert a T ha ih =>
    have haT : a ∉ T := fun h => lt_irrefl a (ha a h)
    rw [Finset.sum_insert haT, Finset.card_insert_of_notMem haT, Finset.sum_range_succ]
    have h1 : (insert a T).filter (fun k => k ≤ a) = insert a T := by
      apply Finset.filter_true_of_mem
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact le_rfl
      · exact (ha x hx).le
    have h2 : ∀ X ∈ T, (insert a T).filter (fun k => k ≤ X) = T.filter (fun k => k ≤ X) := by
      intro X hX
      rw [Finset.filter_insert, if_neg (not_le.2 (ha X hX))]
    rw [h1, Finset.card_insert_of_notMem haT, Finset.sum_congr rfl (fun X hX => by rw [h2 X hX]),
      ih]
    ring

lemma g_pos (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ) :
    0 < 1 - ((m + 2 : ℕ) : ℝ) * p ^ (m + 1) + (((m + 2 : ℕ) : ℝ) - 1) * p ^ (m + 2) := by
  induction m with
  | zero => norm_num; nlinarith
  | succ m ih =>
    have hpm : 0 < p ^ (m + 1) := pow_pos hp0 _
    have key : 1 - ((m + 1 + 2 : ℕ) : ℝ) * p ^ (m + 1 + 1) +
        (((m + 1 + 2 : ℕ) : ℝ) - 1) * p ^ (m + 1 + 2) =
        (1 - ((m + 2 : ℕ) : ℝ) * p ^ (m + 1) + (((m + 2 : ℕ) : ℝ) - 1) * p ^ (m + 2)) +
          ((m : ℝ) + 2) * p ^ (m + 1) * (1 - p) ^ 2 := by
      push_cast; ring
    rw [key]
    have : 0 < ((m : ℝ) + 2) * p ^ (m + 1) * (1 - p) ^ 2 := by
      have : 0 < (1 - p) ^ 2 := by nlinarith
      positivity
    linarith

lemma log_pos' (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) : 0 < Real.log (1 / p) := by
  apply Real.log_pos; rw [lt_one_div (by norm_num) hp0]; simpa using hp1

lemma aSeq_pos (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) (hn : 2 ≤ n) :
    0 < aSeq p n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold aSeq
  have hl := log_pos' p hp0 hp1
  have := g_pos p hp0 hp1 m
  have e : m + 2 - 1 = m + 1 := by omega
  rw [e]
  positivity

lemma aSeq_mono (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) (hn : 2 ≤ n) :
    aSeq p n ≤ aSeq p (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold aSeq
  have hl := log_pos' p hp0 hp1
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 + 1 - 1 = m + 2 := by omega
  rw [e1, e2]
  apply mul_le_mul_of_nonneg_left _ hl.le
  have hpm : 0 < p ^ (m + 1) := pow_pos hp0 _
  have key : 1 - ((m + 2 + 1 : ℕ) : ℝ) * p ^ (m + 2) +
      (((m + 2 + 1 : ℕ) : ℝ) - 1) * p ^ (m + 2 + 1) =
      (1 - ((m + 2 : ℕ) : ℝ) * p ^ (m + 1) + (((m + 2 : ℕ) : ℝ) - 1) * p ^ (m + 2)) +
        ((m : ℝ) + 2) * p ^ (m + 1) * (1 - p) ^ 2 := by
    push_cast; ring
  rw [key]
  have : 0 ≤ ((m : ℝ) + 2) * p ^ (m + 1) * (1 - p) ^ 2 := by positivity
  linarith

lemma aSeq_mono' (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (i M : ℕ) (hi : 2 ≤ i) (hiM : i ≤ M) :
    aSeq p i ≤ aSeq p M := by
  induction M, hiM using Nat.le_induction with
  | base => exact le_rfl
  | succ M hM ih => exact ih.trans (aSeq_mono p hp0 hp1 M (by omega))

lemma aSeq_one (p : ℝ) : aSeq p 1 = 0 := by simp [aSeq]

lemma oa_mem {K : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (σ : Equiv.Perm (Fin K)) :
    oa p σ ∈ MpRank p σ := by
  classical
  have hrel : ∀ (S : DS K) (X : Fin K), relRank σ S X =
      ((S.1.map σ.toEmbedding).filter (fun y => y ≤ σ X)).card := by
    intro S X
    unfold relRank
    rw [Finset.filter_map, Finset.card_map]
    rfl
  have hr1 : ∀ (S : DS K) (X : Fin K), X ∈ S.1 → 1 ≤ relRank σ S X := by
    intro S X hX
    exact Finset.card_pos.2 ⟨X, Finset.mem_filter.2 ⟨hX, le_rfl⟩⟩
  have hmono : ∀ (S : DS K) (X X' : Fin K), X ∈ S.1 → X' ∈ S.1 → σ X < σ X' →
      relRank σ S X < relRank σ S X' := by
    intro S X X' hX hX' hlt
    unfold relRank
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨X', Finset.mem_filter.2 ⟨hX', le_rfl⟩, ?_⟩
      intro h
      exact absurd (Finset.mem_filter.1 h).2 (not_le.2 hlt)
    · intro k hk
      simp only [Finset.mem_filter] at hk ⊢
      exact ⟨hk.1, hk.2.trans hlt.le⟩
  have hc : ∀ S : DS K, 0 < (1 - p) / (1 - p ^ S.1.card) := by
    intro S
    have : p ^ S.1.card < 1 := pow_lt_one₀ hp0.le hp1 (by have := S.2; omega)
    apply div_pos <;> linarith
  -- value comparison
  have hval : ∀ (S : DS K) (X X' : Fin K), X ∈ S.1 → X' ∈ S.1 →
      (oa p σ S X' ≤ oa p σ S X ↔ relRank σ S X ≤ relRank σ S X') := by
    intro S X X' hX hX'
    simp only [oa, if_pos hX, if_pos hX']
    rw [mul_le_mul_iff_right₀ (hc S), pow_le_pow_iff_right_of_lt_one₀ hp0 hp1]
    have := hr1 S X hX; have := hr1 S X' hX'
    omega
  refine ⟨⟨?_, ?_, σ, ?_, ?_⟩, ?_⟩
  · intro S X
    refine ⟨fun hX => ?_, fun hX => ?_⟩
    · simp only [oa, if_pos hX]; have := hc S; positivity
    · simp [oa, hX]
  · intro S
    have hn : (S.1.map σ.toEmbedding).card = S.1.card := Finset.card_map _
    calc ∑ X ∈ S.1, oa p σ S X
        = ∑ X ∈ S.1, (1 - p) / (1 - p ^ S.1.card) *
            (fun y => p ^ (((S.1.map σ.toEmbedding).filter (fun z => z ≤ y)).card - 1)) (σ X) := by
          refine Finset.sum_congr rfl fun X hX => ?_
          simp only [oa, if_pos hX, hrel S X]
      _ = (1 - p) / (1 - p ^ S.1.card) * ∑ y ∈ S.1.map σ.toEmbedding,
            p ^ (((S.1.map σ.toEmbedding).filter (fun z => z ≤ y)).card - 1) := by
          rw [Finset.mul_sum, Finset.sum_map]
          rfl
      _ = 1 := by
          rw [sum_rank (fun j => p ^ (j - 1)), hn]
          simp only [Nat.add_sub_cancel]
          rw [geom_sum_eq hp1.ne]
          have h1 : (1 : ℝ) - p ^ S.1.card ≠ 0 := (hc S).ne' |> fun h => by
            intro h0; rw [h0, div_zero] at h; exact h rfl
          have h2 : p - 1 ≠ 0 := by linarith
          have h3 : (1 : ℝ) - p ≠ 0 := by linarith
          field_simp
          ring
  · intro S X X' hX hX' hne
    rw [hval S X X' hX hX']
    constructor
    · intro hle
      rcases lt_or_gt_of_ne (fun h : σ X = σ X' => hne (σ.injective h)) with h | h
      · exact h
      · exact absurd (hmono S X' X hX' hX h) (not_lt.2 hle)
    · intro h; exact (hmono S X X' hX hX' h).le
  · intro S X X' hX hX' hlt
    have := hmono S X X' hX hX' hlt
    have := hr1 S X hX
    simp only [oa, if_pos hX, if_pos hX']
    rw [mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (hc S).le
    rw [← pow_succ']
    exact pow_le_pow_of_le_one hp0.le hp1.le (by omega)
  · intro S X X' hX hX' hne
    rw [hval S X X' hX hX']
    constructor
    · intro hle
      rcases lt_or_gt_of_ne (fun h : σ X = σ X' => hne (σ.injective h)) with h | h
      · exact h
      · exact absurd (hmono S X' X hX' hX h) (not_lt.2 hle)
    · intro h; exact (hmono S X X' hX hX' h).le

end MTPAux7

namespace MTPAux1i
open RobustPrefLearn.MTP

lemma plog (a b c L : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c)
    (hpos : 0 < a → 0 < b ∧ L = Real.log (a / b)) :
    a * Real.log c + a - c * b ≤ a * L := by
  rcases ha.lt_or_eq with ha | ha
  · obtain ⟨hb, rfl⟩ := hpos ha
    have h1 : Real.log (b * c / a) ≤ b * c / a - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (b * c / a) = Real.log b + Real.log c - Real.log a := by
      rw [Real.log_div (by positivity) ha.ne', Real.log_mul hb.ne' hc.ne']
    rw [h2] at h1
    rw [Real.log_div ha.ne' hb.ne']
    have h3 : a * (b * c / a - 1) = b * c - a := by field_simp
    nlinarith
  · subst ha; simp; positivity

lemma f_nonneg {K : ℕ} {p : ℝ} {f : Pref K} (hf : f ∈ (Mp p : Set (Pref K))) (S : DS K)
    (X : Fin K) : 0 ≤ f S X := by
  by_cases hX : X ∈ S.1
  · exact ((hf.1 S X).1 hX).le
  · exact ((hf.1 S X).2 hX).ge

lemma DS_nonneg {K : ℕ} {p : ℝ} {f g : Pref K} (hf : f ∈ (Mp p : Set (Pref K)))
    (hg : g ∈ (Mp p : Set (Pref K))) (S : DS K) : 0 ≤ DS_ f g S := by
  unfold DS_
  have : ∑ X ∈ S.1, (f S X * Real.log 1 + f S X - 1 * g S X) ≤
      ∑ X ∈ S.1, f S X * Real.log (f S X / g S X) := by
    apply Finset.sum_le_sum
    intro X hX
    exact plog _ _ _ _ (f_nonneg hf S X) (f_nonneg hg S X) one_pos
      (fun _ => ⟨(hg.1 S X).1 hX, rfl⟩)
  have h2 : ∑ X ∈ S.1, (f S X * Real.log 1 + f S X - 1 * g S X) = 0 := by
    simp only [Real.log_one, mul_zero, zero_add, one_mul]
    rw [Finset.sum_sub_distrib, hf.2.1 S, hg.2.1 S, sub_self]
  linarith

end MTPAux1i

namespace MTPAux5
open RobustPrefLearn.MTP

/-- Rankings satisfying (A-3) for the same preference induce the same strict order. -/
lemma order_transfer {K : ℕ} (g : Pref K) (σ τ : Equiv.Perm (Fin K)) (hσ : Ranks g σ)
    (hτ : Ranks g τ) (X X' : Fin K) (hne : X ≠ X') : σ X < σ X' ↔ τ X < τ X' := by
  have hcard : 2 ≤ ({X, X'} : Finset (Fin K)).card := by rw [Finset.card_pair hne]
  set S : DS K := ⟨{X, X'}, hcard⟩
  have h1 : X ∈ S.1 := by simp [S]
  have h2 : X' ∈ S.1 := by simp [S]
  rw [← hσ S X X' h1 h2 hne, hτ S X X' h1 h2 hne]

lemma psep_transfer {K : ℕ} (p : ℝ) (g : Pref K) (σ τ : Equiv.Perm (Fin K)) (hσ : Ranks g σ)
    (hτ : Ranks g τ) (hps : PSep p g σ) : PSep p g τ := by
  intro S X X' hX hX' hlt
  have hne : X ≠ X' := fun e => by rw [e] at hlt; exact lt_irrefl _ hlt
  exact hps S X X' hX hX' ((order_transfer g σ τ hσ hτ X X' hne).2 hlt)

lemma psep_of_rank {K : ℕ} (p : ℝ) (g : Pref K) (τ : Equiv.Perm (Fin K))
    (hg : g ∈ MpRank p τ) : PSep p g τ := by
  obtain ⟨σ0, hR0, hP0⟩ := hg.1.2.2
  exact psep_transfer p g σ0 τ hR0 hg.2 hP0

lemma sum_rank {K : ℕ} (g : ℕ → ℝ) (T : Finset (Fin K)) :
    ∑ X ∈ T, g (T.filter (fun k => k ≤ X)).card = ∑ j ∈ Finset.range T.card, g (j + 1) := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert a T ha ih =>
    have haT : a ∉ T := fun h => lt_irrefl a (ha a h)
    rw [Finset.sum_insert haT, Finset.card_insert_of_notMem haT, Finset.sum_range_succ]
    have h1 : (insert a T).filter (fun k => k ≤ a) = insert a T := by
      apply Finset.filter_true_of_mem
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact le_rfl
      · exact (ha x hx).le
    have h2 : ∀ X ∈ T, (insert a T).filter (fun k => k ≤ X) = T.filter (fun k => k ≤ X) := by
      intro X hX
      rw [Finset.filter_insert, if_neg (not_le.2 (ha X hX))]
    rw [h1, Finset.card_insert_of_notMem haT, Finset.sum_congr rfl (fun X hX => by rw [h2 X hX]),
      ih]
    ring

lemma relRank_one {K : ℕ} (S : DS K) (X : Fin K) :
    relRank (1 : Equiv.Perm (Fin K)) S X = (S.1.filter (fun k => k ≤ X)).card := by
  unfold relRank
  congr 1

lemma hv {K : ℕ} (m k : Fin K) : ((sigmaHat m) k).val =
    if k.val < m.val then k.val + 1 else if k.val = m.val then 0 else k.val := by
  unfold sigmaHat
  by_cases h : k ≤ m
  · rw [Fin.coe_cycleRange_of_le h]
    by_cases h' : k = m
    · subst h'; simp
    · have : k.val < m.val := lt_of_le_of_ne h (fun e => h' (Fin.ext e))
      rw [if_neg h', if_pos this]
  · rw [Fin.cycleRange_of_gt (not_le.1 h)]
    have : ¬ k.val < m.val := fun e => h (le_of_lt e)
    have : ¬ k.val = m.val := fun e => h (le_of_eq (Fin.ext e))
    simp_all

lemma relRank_hat {K : ℕ} (m : Fin K) (S : DS K) (X : Fin K) :
    relRank (sigmaHat m) S X =
      if X < m then (S.1.filter (fun k => k ≤ X)).card + (if m ∈ S.1 then 1 else 0)
      else if X = m then (if m ∈ S.1 then 1 else 0)
      else (S.1.filter (fun k => k ≤ X)).card := by
  unfold relRank
  simp only [Finset.card_filter]
  have key : ∀ k : Fin K, (if sigmaHat m k ≤ sigmaHat m X then 1 else 0 : ℕ) =
      if X < m then (if k ≤ X then 1 else 0) + (if k = m then 1 else 0)
      else if X = m then (if k = m then 1 else 0)
      else (if k ≤ X then 1 else 0) := by
    intro k
    simp only [Fin.le_def, hv m k, hv m X]
    simp only [Fin.lt_def, Fin.ext_iff]
    split_ifs <;> omega
  rw [Finset.sum_congr rfl (fun k _ => key k)]
  split_ifs <;> simp_all [Finset.sum_add_distrib, Finset.sum_ite_eq']

/-- Split a sum over `S ∋ k` into the parts before `k`, at `k` and after `k`. -/
lemma sum_split {K : ℕ} (S : Finset (Fin K)) (k : Fin K) (hk : k ∈ S) (F : Fin K → ℝ) :
    ∑ X ∈ S, F X = ∑ X ∈ S.filter (fun X => X < k), F X + F k +
      ∑ X ∈ S.filter (fun X => k < X), F X := by
  classical
  have : ∀ X, F X = (if X < k then F X else 0) + (if X = k then F X else 0) +
      (if k < X then F X else 0) := by
    intro X
    rcases lt_trichotomy X k with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.2 h.le]
  rw [Finset.sum_congr rfl (fun X _ => this X), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_filter, Finset.sum_filter, Finset.sum_ite_eq' S k F, if_pos hk]

end MTPAux5

open RobustPrefLearn.MTP in
theorem solution (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (k : Fin K)
    (hk : 1 ≤ k.val) (S : DS K) :
    oa p (1 : Equiv.Perm (Fin K)) ∈ MpRank p (1 : Equiv.Perm (Fin K)) ∧
    oa p (sigmaHat k) ∈ MpRank p (sigmaHat k) ∧
    ∀ f ∈ MpRank p (1 : Equiv.Perm (Fin K)), ∀ g ∈ MpRank p (sigmaHat k),
      DS_ (oa p (1 : Equiv.Perm (Fin K))) (oa p (sigmaHat k)) S ≤ DS_ f g S := by
  classical
  refine ⟨MTPAux7.oa_mem p hp0 hp1 1, MTPAux7.oa_mem p hp0 hp1 (sigmaHat k), fun f hf g hg => ?_⟩
  rw [lemma_6 K hK p hp0 hp1 k hk S]
  by_cases hkS : k ∈ S.1
  swap
  · rw [if_neg hkS]; exact MTPAux1i.DS_nonneg hf.1 hg.1 S
  rw [if_pos hkS]
  set n := S.1.card with hn
  have hn2 : 2 ≤ n := S.2
  set r : Fin K → ℕ := fun X => (S.1.filter (fun j => j ≤ X)).card with hr
  have hrel : ∀ X, relRank (1 : Equiv.Perm (Fin K)) S X = r X := fun X => MTPAux5.relRank_one S X
  set i := r k with hi
  have hr1 : ∀ X ∈ S.1, 1 ≤ r X := fun X hX => by rw [← hrel]; exact MTPAux10.rank_ge_one 1 S X hX
  have hi1 : 1 ≤ i := hr1 k hkS
  have hin : i ≤ n := Finset.card_le_card (Finset.filter_subset _ _)
  rw [hrel k]
  -- `c_X = f^OA_{σ*}(X|S)/f^OA_{σ̂_k}(X|S)`
  have hc : 0 < (1 - p) / (1 - p ^ n) := by
    have : p ^ n < 1 := pow_lt_one₀ hp0.le hp1 (by omega)
    apply div_pos <;> linarith
  set c : Fin K → ℝ := fun X => oa p 1 S X / oa p (sigmaHat k) S X with hcdef
  have hlogc : ∀ X ∈ S.1, Real.log (c X) =
      if X < k then Real.log (1 / p) else if X = k then ((i - 1 : ℕ) : ℝ) * Real.log p else 0 := by
    intro X hX
    simp only [hcdef, oa, if_pos hX]
    rw [← hn, mul_div_mul_left _ _ hc.ne', Real.log_div (pow_pos hp0 _).ne' (pow_pos hp0 _).ne',
      Real.log_pow, Real.log_pow, MTPAux5.relRank_hat, if_pos hkS, hrel X]
    have := hr1 X hX
    split_ifs with h1 h2
    · have e : r X + 1 - 1 = (r X - 1) + 1 := by omega
      rw [e, one_div, Real.log_inv]; push_cast; ring
    · subst h2; simp [hi]
    · simp only [hr, sub_self]
  have hcpos : ∀ X ∈ S.1, 0 < c X := by
    intro X hX
    simp only [hcdef, oa, if_pos hX]
    positivity
  -- Step 1: `D_S(f‖g) ≥ ∑ f log c`
  have hf1 := MTPAux1i.f_nonneg hf.1
  have hg1 := MTPAux1i.f_nonneg hg.1
  have hratio := MTPAux10.ratio_sum_le_one p hp0 hp1 g hg.1 (sigmaHat k)
    (MTPAux5.psep_of_rank p g _ hg) 1 S
  have hstep1 : ∑ X ∈ S.1, f S X * Real.log (c X) ≤ DS_ f g S := by
    unfold DS_
    have : ∑ X ∈ S.1, (f S X * Real.log (c X) + f S X - c X * g S X) ≤
        ∑ X ∈ S.1, f S X * Real.log (f S X / g S X) :=
      Finset.sum_le_sum fun X hX => MTPAux1i.plog _ _ _ _ (hf1 S X) (hg1 S X) (hcpos X hX)
        (fun _ => ⟨(hg.1.1 S X).1 hX, rfl⟩)
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hf.1.2.1 S] at this
    have h2 : ∑ X ∈ S.1, c X * g S X ≤ 1 := by
      calc _ = ∑ X ∈ S.1, g S X * (oa p 1 S X / oa p (sigmaHat k) S X) := by
            refine Finset.sum_congr rfl fun X _ => ?_; simp only [hcdef]; ring
        _ ≤ 1 := hratio
    linarith
  -- Step 2: `∑ f log c = log(1/p) (A - (i-1) f_k)`
  set A := ∑ X ∈ S.1.filter (fun X => X < k), f S X with hA
  set B := ∑ X ∈ S.1.filter (fun X => k < X), f S X with hB
  have hsumf : A + f S k + B = 1 := by
    rw [hA, hB, ← MTPAux5.sum_split S.1 k hkS (fun X => f S X)]; exact hf.1.2.1 S
  have hlogp : Real.log p = -Real.log (1 / p) := by rw [one_div, Real.log_inv, neg_neg]
  have hstep2 : ∑ X ∈ S.1, f S X * Real.log (c X) =
      Real.log (1 / p) * (A - ((i - 1 : ℕ) : ℝ) * f S k) := by
    rw [MTPAux5.sum_split S.1 k hkS (fun X => f S X * Real.log (c X))]
    have e1 : ∑ X ∈ S.1.filter (fun X => X < k), f S X * Real.log (c X) =
        ∑ X ∈ S.1.filter (fun X => X < k), f S X * Real.log (1 / p) := by
      refine Finset.sum_congr rfl fun X hX => ?_
      rw [hlogc X (Finset.mem_filter.1 hX).1, if_pos (Finset.mem_filter.1 hX).2]
    have e2 : ∑ X ∈ S.1.filter (fun X => k < X), f S X * Real.log (c X) = 0 := by
      apply Finset.sum_eq_zero
      intro X hX
      rw [hlogc X (Finset.mem_filter.1 hX).1, if_neg (not_lt.2 (Finset.mem_filter.1 hX).2.le),
        if_neg (Finset.mem_filter.1 hX).2.ne', mul_zero]
    have e3 : f S k * Real.log (c k) = f S k * (((i - 1 : ℕ) : ℝ) * Real.log p) := by
      rw [hlogc k hkS, if_neg (lt_irrefl k), if_pos rfl]
    rw [e1, e2, e3, ← Finset.sum_mul, hlogp]
    ring
  -- Step 3: chain bounds
  have hps : PSep p f (1 : Equiv.Perm (Fin K)) := MTPAux5.psep_of_rank p f 1 hf
  have hrr : ∀ X, relRank (1 : Equiv.Perm (Fin K)) S X = r X := hrel
  set P := p ^ (i - 1) with hP
  have hlow : ∀ X ∈ S.1.filter (fun X => X < k), f S k * p ^ (r X - 1) ≤ P * f S X := by
    intro X hX
    obtain ⟨hXS, hXk⟩ := Finset.mem_filter.1 hX
    have hlt : r X < i := by
      rw [hi, ← hrr, ← hrr]; exact MTPAux10.rank_strict 1 S X k hkS (by simpa using hXk)
    have := MTPAux10.psep_chain p hp0 f 1 hps hf1 S (i - r X) k X hkS hXS
      (by rw [hrr, hrr]; omega)
    have hX1 := hr1 X hXS
    calc f S k * p ^ (r X - 1) ≤ p ^ (i - r X) * f S X * p ^ (r X - 1) := by gcongr
      _ = P * f S X := by
        rw [hP, show i - 1 = (i - r X) + (r X - 1) by omega, pow_add]; ring
  have hup : ∀ X ∈ S.1.filter (fun X => k < X), P * f S X ≤ f S k * p ^ (r X - 1) := by
    intro X hX
    obtain ⟨hXS, hXk⟩ := Finset.mem_filter.1 hX
    have hlt : i < r X := by
      rw [hi, ← hrr, ← hrr]; exact MTPAux10.rank_strict 1 S k X hXS (by simpa using hXk)
    have := MTPAux10.psep_chain p hp0 f 1 hps hf1 S (r X - i) X k hXS hkS
      (by rw [hrr, hrr]; omega)
    calc P * f S X ≤ P * (p ^ (r X - i) * f S k) := by gcongr
      _ = f S k * p ^ (r X - 1) := by
        rw [hP, show r X - 1 = (i - 1) + (r X - i) by omega, pow_add]; ring
  -- the geometric sums
  have hT : ∀ X ∈ S.1.filter (fun X => X < k),
      r X = ((S.1.filter (fun X => X < k)).filter (fun j => j ≤ X)).card := by
    intro X hX
    simp only [hr]
    congr 1
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, lt_of_le_of_lt h2 (Finset.mem_filter.1 hX).2⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
  have hcardT : (S.1.filter (fun X => X < k)).card = i - 1 := by
    have : S.1.filter (fun j => j ≤ k) = insert k (S.1.filter (fun X => X < k)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        rcases lt_or_eq_of_le h2 with h | h
        · exact Or.inr ⟨h1, h⟩
        · exact Or.inl h
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨hkS, le_rfl⟩
        · exact ⟨h1, h2.le⟩
    have h2 : i = (S.1.filter (fun j => j ≤ k)).card := rfl
    rw [this, Finset.card_insert_of_notMem (by simp)] at h2
    omega
  have hSα : ∑ X ∈ S.1.filter (fun X => X < k), p ^ (r X - 1) = (1 - P) / (1 - p) := by
    rw [Finset.sum_congr rfl (fun X hX => by rw [hT X hX])]
    rw [MTPAux5.sum_rank (fun j => p ^ (j - 1)), hcardT]
    simp only [Nat.add_sub_cancel]
    rw [geom_sum_eq hp1.ne, hP]
    have : p - 1 ≠ 0 := by linarith
    have : 1 - p ≠ 0 := by linarith
    field_simp
    ring
  have htot : ∑ X ∈ S.1, p ^ (r X - 1) = (1 - p ^ n) / (1 - p) := by
    rw [MTPAux5.sum_rank (fun j => p ^ (j - 1)) S.1]
    simp only [Nat.add_sub_cancel]
    rw [geom_sum_eq hp1.ne]
    have : p - 1 ≠ 0 := by linarith
    have : 1 - p ≠ 0 := by linarith
    field_simp
    ring
  have hSγ : ∑ X ∈ S.1.filter (fun X => k < X), p ^ (r X - 1) = (p ^ i - p ^ n) / (1 - p) := by
    have := MTPAux5.sum_split S.1 k hkS (fun X => p ^ (r X - 1))
    rw [htot, hSα] at this
    have hpi : p ^ i = P * p := by rw [hP, ← pow_succ]; congr 1; omega
    have h1p : 1 - p ≠ 0 := by linarith
    rw [hpi]
    field_simp at this ⊢
    simp only [← hi] at this
    linarith
  have hAlow : f S k * ((1 - P) / (1 - p)) ≤ P * A := by
    rw [← hSα, Finset.mul_sum, hA, Finset.mul_sum]
    exact Finset.sum_le_sum hlow
  have hBup : P * B ≤ f S k * ((p ^ i - p ^ n) / (1 - p)) := by
    rw [← hSγ, hB, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum hup
  -- Step 4: the algebra
  set κ := (1 - (i : ℝ) * p ^ (i - 1) + ((i : ℝ) - 1) * p ^ i) / (1 - p ^ n) with hκ
  have hpn : p ^ n < 1 := pow_lt_one₀ hp0.le hp1 (by omega)
  have hPpos : 0 < P := pow_pos hp0 _
  have hpi : p ^ i = P * p := by rw [hP, ← pow_succ]; congr 1; omega
  have hgi : 0 ≤ 1 - (i : ℝ) * p ^ (i - 1) + ((i : ℝ) - 1) * p ^ i := by
    rcases (show i = 1 ∨ 2 ≤ i by omega) with h | h
    · rw [h]; simp
    · have := MTPAux7.g_pos p hp0 hp1 (i - 2)
      have e : i - 2 + 2 = i := by omega
      have e2 : i - 2 + 1 = i - 1 := by omega
      rw [e, e2] at this
      linarith
  have hκ0 : 0 ≤ κ := div_nonneg hgi (by linarith)
  have hκ1 : κ ≤ 1 := by
    rw [hκ, div_le_one (by linarith)]
    have hpn' : p ^ n ≤ p ^ i := pow_le_pow_of_le_one hp0.le hp1.le hin
    have : (1 : ℝ) ≤ i := by exact_mod_cast hi1
    have hPle : P * p ≤ P := by nlinarith
    rw [hpi]
    nlinarith
  have hkey : (1 - P) / (1 - p) - ((i - 1 : ℕ) : ℝ) * P -
      κ * ((1 - P) / (1 - p) + P + (p ^ i - p ^ n) / (1 - p)) = 0 := by
    rw [hκ, hpi]
    have h1p : 1 - p ≠ 0 := by linarith
    have h1pn : 1 - p ^ n ≠ 0 := by linarith
    have hcast : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by rw [Nat.cast_sub hi1]; simp
    rw [hcast]
    have hPi : p ^ (i - 1) = P := rfl
    rw [hPi]
    field_simp
    ring
  have hfk := hf1 S k
  have hmain : κ ≤ A - ((i - 1 : ℕ) : ℝ) * f S k := by
    have hB' : B = 1 - A - f S k := by linarith
    have e1 : 0 ≤ (1 - κ) * (P * A - f S k * ((1 - P) / (1 - p))) :=
      mul_nonneg (by linarith) (by linarith)
    have e2 : 0 ≤ κ * (f S k * ((p ^ i - p ^ n) / (1 - p)) - P * B) :=
      mul_nonneg hκ0 (by linarith)
    have e3 : P * (A - ((i - 1 : ℕ) : ℝ) * f S k - κ) =
        (1 - κ) * (P * A - f S k * ((1 - P) / (1 - p))) +
        κ * (f S k * ((p ^ i - p ^ n) / (1 - p)) - P * B) +
        f S k * ((1 - P) / (1 - p) - ((i - 1 : ℕ) : ℝ) * P -
          κ * ((1 - P) / (1 - p) + P + (p ^ i - p ^ n) / (1 - p))) := by
      rw [hB']; ring
    rw [hkey, mul_zero, add_zero] at e3
    have : 0 ≤ P * (A - ((i - 1 : ℕ) : ℝ) * f S k - κ) := by rw [e3]; linarith
    have := (mul_nonneg_iff_of_pos_left hPpos).1 this
    linarith
  -- conclusion
  have hL : 0 < Real.log (1 / p) := by
    apply Real.log_pos; rw [lt_one_div (by norm_num) hp0]; simpa using hp1
  calc aSeq p i / bSeq p n = Real.log (1 / p) * κ := by
        unfold aSeq bSeq; rw [hκ]; ring
    _ ≤ Real.log (1 / p) * (A - ((i - 1 : ℕ) : ℝ) * f S k) := by gcongr
    _ = ∑ X ∈ S.1, f S X * Real.log (c X) := hstep2.symm
    _ ≤ DS_ f g S := hstep1
