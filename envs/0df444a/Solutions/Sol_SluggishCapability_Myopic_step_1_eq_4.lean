-- Prove2me | solution 1 for SluggishCapability.Myopic.step_1_eq_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:04:57.310859+00:00
-- url     : https://prove2.me/submissions/2e4766ee-1647-4f24-b0ce-dd6f92b9ff57

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_SluggishCapability_Myopic_Setting

open MarkovMixing

open SluggishCapability.Myopic in
theorem solution {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (f : S → ℕ) (M : ℕ) (hP : IsStochastic P) (hM : ∀ s, f s ≤ M)
    (ν : Fin (M + 1) × S → ℝ) (hν : IsStationary (extKernel P f M) ν) :
    ∑ x : Fin (M + 1) × S, ∑ s' : S,
        (if (x.1 : ℕ) < f s' then ν x * P x.2 s' * ((x.1 : ℝ) + 1) else 0) =
      ∑ x : Fin (M + 1) × S, ∑ s' : S,
        (if f s' < (x.1 : ℕ) then ν x * P x.2 s' * (x.1 : ℝ) else 0) := by
  have hstep : ∀ m d, m ≤ M → d ≤ M → myopicStep m d ≤ M := by
    intro m d hm hd
    unfold myopicStep
    split_ifs <;> omega
  have hcol : ∀ (m : Fin (M + 1)) (s' : S) (cc : ℝ) (g : ℕ → ℝ),
      ∑ m' : Fin (M + 1), (if (m' : ℕ) = myopicStep m (f s') then cc else 0) * g m' =
        cc * g (myopicStep m (f s')) := by
    intro m s' cc g
    have hj : myopicStep m (f s') < M + 1 :=
      Nat.lt_succ_of_le (hstep _ _ (Nat.lt_succ_iff.mp m.2) (hM s'))
    rw [Finset.sum_eq_single (⟨_, hj⟩ : Fin (M + 1))]
    · simp
    · intro b _ hb
      rw [if_neg, zero_mul]
      intro h
      exact hb (Fin.ext h)
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hstat : ∀ g : ℕ → ℝ, ∑ x : Fin (M + 1) × S, ∑ s' : S,
      ν x * P x.2 s' * (g (myopicStep x.1 (f s')) - g x.1) = 0 := by
    intro g
    have hA : ∑ y : Fin (M + 1) × S, ν y * g y.1 =
        ∑ x : Fin (M + 1) × S, ∑ s' : S, ν x * P x.2 s' * g (myopicStep x.1 (f s')) := by
      conv_lhs => rw [← hν.2]
      simp only [Matrix.vecMul, dotProduct]
      conv_lhs => simp only [Finset.sum_mul]; rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun s' _ => ?_
      rw [← hcol x.1 s' (ν x * P x.2 s') g]
      refine Finset.sum_congr rfl fun m' _ => ?_
      simp only [extKernel]
      split_ifs <;> ring
    have hB : ∑ x : Fin (M + 1) × S, ∑ s' : S, ν x * P x.2 s' * g x.1 =
        ∑ y : Fin (M + 1) × S, ν y * g y.1 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      have : ∑ s', ν x * P x.2 s' * g x.1 = ν x * g x.1 * ∑ s', P x.2 s' := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s' _ => ?_; ring
      rw [this, hP.2 x.2, mul_one]
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← hA, hB, sub_self]
  have E1 := hstat (fun k => (k : ℝ))
  have E2 := hstat (fun k => (k : ℝ) ^ 2)
  have hpt : ∀ (x : Fin (M + 1) × S) (s' : S),
      (if (x.1 : ℕ) < f s' then ν x * P x.2 s' * ((x.1 : ℝ) + 1) else 0) -
        (if f s' < (x.1 : ℕ) then ν x * P x.2 s' * (x.1 : ℝ) else 0) =
      (ν x * P x.2 s' * (((myopicStep x.1 (f s') : ℕ) : ℝ) - ((x.1 : ℕ) : ℝ)) +
        ν x * P x.2 s' * (((myopicStep x.1 (f s') : ℕ) : ℝ) ^ 2 - ((x.1 : ℕ) : ℝ) ^ 2)) / 2 := by
    intro x s'
    unfold myopicStep
    rcases lt_trichotomy (x.1 : ℕ) (f s') with h | h | h
    · rw [if_pos h, if_neg (by omega), if_pos h]
      push_cast; ring
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h.symm]
      ring
    · rw [if_neg (by omega), if_pos h, if_neg (by omega), if_neg (by omega)]
      rw [Nat.cast_sub (by omega : 1 ≤ (x.1 : ℕ))]
      push_cast; ring
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib, hpt]
  simp only [add_div, Finset.sum_add_distrib, ← Finset.sum_div]
  rw [E1, E2]
  simp
