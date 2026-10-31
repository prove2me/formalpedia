-- Prove2me | solution 1 for RobustPrefLearn.MTP.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T14:14:42.359008+00:00
-- url     : https://prove2.me/submissions/0dfce722-e782-45a5-8c7a-6228ccfb55b0

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_OA

open scoped ENNReal

namespace MTPAux6
open RobustPrefLearn.MTP

/-- Summing a function of the (1-based) rank of each element inside a finset. -/
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
    simp only [Fin.lt_def, Fin.le_def, Fin.ext_iff]
    split_ifs <;> omega
  rw [Finset.sum_congr rfl (fun k _ => key k)]
  split_ifs <;> simp_all [Finset.sum_add_distrib, Finset.sum_ite_eq']

end MTPAux6

open RobustPrefLearn.MTP in
theorem solution (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (m : Fin K)
    (hm : 1 ≤ m.val) (S : DS K) :
    DS_ (oa p (1 : Equiv.Perm (Fin K))) (oa p (sigmaHat m)) S =
      if m ∈ S.1 then aSeq p (relRank (1 : Equiv.Perm (Fin K)) S m) / bSeq p S.1.card
      else 0 := by
  classical
  set n := S.1.card with hn
  set c : ℝ := (1 - p) / (1 - p ^ n) with hc
  have hn2 : 2 ≤ n := S.2
  have hpn : p ^ n < 1 := pow_lt_one₀ hp0.le hp1 (by omega)
  have hc0 : 0 < c := div_pos (by linarith) (by linarith)
  set r : Fin K → ℕ := fun X => (S.1.filter (fun k => k ≤ X)).card with hr
  have hr1 : ∀ X ∈ S.1, 1 ≤ r X := by
    intro X hX
    exact Finset.card_pos.2 ⟨X, Finset.mem_filter.2 ⟨hX, le_rfl⟩⟩
  -- each summand
  have hterm : ∀ X ∈ S.1, oa p (1 : Equiv.Perm (Fin K)) S X *
      Real.log (oa p (1 : Equiv.Perm (Fin K)) S X / oa p (sigmaHat m) S X) =
      c * p ^ (r X - 1) *
        ((((r X - 1 : ℕ) : ℝ) - ((relRank (sigmaHat m) S X - 1 : ℕ) : ℝ)) * Real.log p) := by
    intro X hX
    simp only [oa, if_pos hX, MTPAux6.relRank_one]
    rw [← hc]
    congr 1
    rw [mul_div_mul_left _ _ hc0.ne', Real.log_div (pow_pos hp0 _).ne' (pow_pos hp0 _).ne',
      Real.log_pow, Real.log_pow]
    ring
  unfold DS_
  rw [Finset.sum_congr rfl hterm]
  by_cases hmS : m ∈ S.1
  · rw [if_pos hmS]
    have hterm2 : ∀ X ∈ S.1, c * p ^ (r X - 1) *
        ((((r X - 1 : ℕ) : ℝ) - ((relRank (sigmaHat m) S X - 1 : ℕ) : ℝ)) * Real.log p) =
        if X < m then -(c * Real.log p) * p ^ (r X - 1)
        else if X = m then c * p ^ (r m - 1) * (((r m - 1 : ℕ) : ℝ) * Real.log p) else 0 := by
      intro X hX
      rw [MTPAux6.relRank_hat, if_pos hmS]
      have := hr1 X hX
      split_ifs with h1 h2
      · have e : r X + 1 - 1 = (r X - 1) + 1 := by omega
        simp only [hr] at e ⊢
        rw [e]; push_cast; ring
      · subst h2; simp
      · simp only [hr, sub_self, zero_mul, mul_zero]
    rw [Finset.sum_congr rfl hterm2, Finset.sum_ite, Finset.sum_ite, ← Finset.mul_sum]
    set T := S.1.filter (fun X => X < m) with hT
    have hTr : ∀ X ∈ T, r X = (T.filter (fun k => k ≤ X)).card := by
      intro X hX
      simp only [hr]
      congr 1
      ext k
      simp only [hT, Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, lt_of_le_of_lt h2 (Finset.mem_filter.1 hX).2⟩, h2⟩
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    have hsumT : ∑ X ∈ T, p ^ (r X - 1) = ∑ j ∈ Finset.range T.card, p ^ j := by
      rw [Finset.sum_congr rfl (fun X hX => by rw [hTr X hX])]
      rw [MTPAux6.sum_rank (fun j => p ^ (j - 1)) T]
      simp
    have hrm : r m = T.card + 1 := by
      simp only [hr, hT]
      have : S.1.filter (fun k => k ≤ m) = insert m (S.1.filter (fun X => X < m)) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          rcases lt_or_eq_of_le h2 with h | h
          · exact Or.inr ⟨h1, h⟩
          · exact Or.inl h
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨hmS, le_rfl⟩
          · exact ⟨h1, h2.le⟩
      rw [this, Finset.card_insert_of_notMem (by simp)]
    have hfilt : (S.1.filter (fun X => ¬ X < m)).filter (fun X => X = m) = {m} := by
      ext k; simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨_, h⟩; exact h
      · rintro rfl; exact ⟨⟨hmS, lt_irrefl _⟩, rfl⟩
    rw [hfilt, Finset.sum_singleton, hsumT]
    simp only [Finset.sum_const_zero, add_zero]
    rw [MTPAux6.relRank_one]
    change _ = aSeq p (r m) / bSeq p n
    rw [hrm]
    set N := T.card
    rw [geom_sum_eq hp1.ne]
    unfold aSeq bSeq
    simp only [Nat.add_sub_cancel]
    rw [hc, Real.log_div one_ne_zero hp0.ne', Real.log_one]
    have h1p : (1 : ℝ) - p ≠ 0 := by linarith
    have h1pn : (1 : ℝ) - p ^ n ≠ 0 := by linarith
    have hp1' : p - 1 ≠ 0 := by linarith
    field_simp
    push_cast
    ring
  · rw [if_neg hmS]
    apply Finset.sum_eq_zero
    intro X hX
    rw [MTPAux6.relRank_hat, if_neg hmS]
    have hXm : X ≠ m := fun h => hmS (h ▸ hX)
    rw [if_neg hXm]
    split_ifs <;> simp [hr]
