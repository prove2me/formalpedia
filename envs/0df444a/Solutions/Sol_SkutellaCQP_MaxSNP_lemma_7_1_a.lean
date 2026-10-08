-- Prove2me | solution 1 for SkutellaCQP.MaxSNP.lemma_7_1_a
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:15:09.711785+00:00
-- url     : https://prove2.me/submissions/5251651e-b07e-4e3c-9771-55e29ade1613

import Mathlib
import Definitions.Def_SkutellaCQP_MaxSNP_Setting

open SkutellaCQP.MaxSNP Finset

theorem solution {n m : ℕ} (I : Occ3Max3Sat n m) (hI : I.IsValid)
    (S : Sched n m) (hS : Feasible I S) :
    (4 * n + 4 * m : ℝ) - VAL S ≤ satCount I (SAT S) := by
  classical
  let v : Fin n → ℝ := fun x => S.start (Sum.inl x)
  let c : Fin m → ℝ := fun a => S.start (Sum.inr a)
  let x : Fin m → Fin n := fun a => (S.mach (Sum.inr a)).1
  have hv (a : Fin n) : 0 ≤ v a := hS.2.1 (Sum.inl a)
  have hc (a : Fin m) : 3 ≤ c a := hS.2.1 (Sum.inr a)
  have hm (a : Fin m) (hu : ¬ Satisfies (SAT S) (I.clause a)) :
      S.mach (Sum.inl (x a)) = S.mach (Sum.inr a) := by
    have he : (x a, !(S.mach (Sum.inr a)).2) ∈ I.clause a := hS.1 (Sum.inr a)
    have hb : (S.mach (Sum.inl (x a))).2 ≠ !(S.mach (Sum.inr a)).2 := by
      intro hh
      exact hu ⟨(x a, !(S.mach (Sum.inr a)).2), he, hh⟩
    have heq : (S.mach (Sum.inl (x a))).2 = (S.mach (Sum.inr a)).2 := by
      cases ha : (S.mach (Sum.inl (x a))).2 <;>
        cases hb' : (S.mach (Sum.inr a)).2 <;> simp_all
    exact Prod.ext (hS.1 (Sum.inl (x a))) heq
  have hpoint (a : Fin m) :
      (if Satisfies (SAT S) (I.clause a) then (0 : ℝ) else 1) ≤ c a - 3 + v (x a) / 3 := by
    by_cases hs : Satisfies (SAT S) (I.clause a)
    · simp only [if_pos hs]
      linarith [hv (x a), hc a]
    · simp only [if_neg hs]
      have ho := hS.2.2 (Sum.inl (x a)) (Sum.inr a) (by simp) (hm a hs)
      change v (x a) + 4 ≤ c a ∨ c a + 0 ≤ v (x a) at ho
      rcases ho with ho | ho <;> linarith [hv (x a), hc a]
  have hcount (a : Fin n) : (univ.filter fun b => x b = a).card ≤ 3 := by
    calc
      (univ.filter fun b => x b = a).card = ∑ b : Fin m, if x b = a then 1 else 0 := by simp [sum_boole]
      _ ≤ ∑ b, ((I.clause b).filter fun ℓ => ℓ.1 = a).card := by
        apply sum_le_sum
        intro b hb
        split_ifs with he
        · apply Nat.succ_le_iff.mpr
          apply card_pos.mpr
          exact ⟨(x b, !(S.mach (Sum.inr b)).2), mem_filter.mpr ⟨hS.1 (Sum.inr b), he⟩⟩
        · exact Nat.zero_le _
      _ ≤ 3 := hI.2.1 a
  have hcharge : ∑ b : Fin m, v (x b) ≤ 3 * ∑ a : Fin n, v a := by
    have heq : ∑ b : Fin m, v (x b) = ∑ a : Fin n, ((univ.filter fun b => x b = a).card : ℝ) * v a := by
      calc
        _ = ∑ b : Fin m, ∑ a : Fin n, if x b = a then v a else 0 := by simp
        _ = ∑ a : Fin n, ∑ b : Fin m, if x b = a then v a else 0 := sum_comm
        _ = _ := by simp [← sum_filter]
    rw [heq, mul_sum]
    apply sum_le_sum
    intro a ha
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount a) (hv a)
  have htot := sum_le_sum (fun a (_ : a ∈ (univ : Finset (Fin m))) => hpoint a)
  have hsat : (∑ a : Fin m, if Satisfies (SAT S) (I.clause a) then (0 : ℝ) else 1) =
      (m : ℝ) - satCount I (SAT S) := by
    have heq : (∑ a : Fin m, if Satisfies (SAT S) (I.clause a) then (0 : ℝ) else 1) +
        (∑ a : Fin m, if Satisfies (SAT S) (I.clause a) then (1 : ℝ) else 0) = m := by
      rw [← sum_add_distrib]
      have heach (a : Fin m) :
          (if Satisfies (SAT S) (I.clause a) then (0 : ℝ) else 1) +
          (if Satisfies (SAT S) (I.clause a) then (1 : ℝ) else 0) = 1 := by
        split_ifs <;> norm_num
      simp_rw [heach]
      simp
    have hcard : (∑ a : Fin m, if Satisfies (SAT S) (I.clause a) then (1 : ℝ) else 0) =
        satCount I (SAT S) := by simp [satCount, sum_boole]
    rw [hcard] at heq
    linarith
  have hval : VAL S = (∑ a : Fin n, v a) + 4 * n + ∑ a : Fin m, c a := by
    simp [VAL, Fintype.sum_sum_type, ptime, v, c, sum_add_distrib, mul_comm]
    ring
  rw [hsat] at htot
  simp only [sum_add_distrib, sum_sub_distrib, ← sum_div, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at htot
  rw [hval]
  linarith

#print axioms solution
