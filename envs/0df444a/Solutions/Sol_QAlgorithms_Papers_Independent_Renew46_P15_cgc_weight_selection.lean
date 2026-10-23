-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P15.cgc_weight_selection
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T15:17:50.166978+00:00
-- url     : https://prove2.me/submissions/39b163ff-4982-4ae6-849c-10cf70798ddb

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P15

noncomputable section

open scoped BigOperators Matrix

attribute [local instance] Classical.propDecidable

namespace X6R15W

open QAlgorithms.Papers.Independent.Renew46.P15

theorem tensor_diag {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (a : A → ℝ) (b : B → ℝ) (r q : A × B) :
    tensorGeneratorMatrix (Matrix.diagonal a) (Matrix.diagonal b) r q =
      if r = q then a q.1 + b q.2 else 0 := by
  obtain ⟨r1, r2⟩ := r; obtain ⟨q1, q2⟩ := q
  simp only [tensorGeneratorMatrix, Matrix.diagonal_apply, Prod.mk.injEq]
  by_cases h1 : r1 = q1 <;> by_cases h2 : r2 = q2 <;> simp [h1, h2]

theorem coupled_diag {n r : ℕ} (t : Fin r → GTTopRow n) (i : Fin (n + 1))
    (p q : (j : Fin r) × Pattern (t j)) :
    coupledMatrix t (fun u => Matrix.diagonal fun m => zWeight m i) p q =
      if p = q then zWeight p.2 i else 0 := by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [coupledMatrix]
  by_cases h : p1 = q1
  · subst h
    by_cases h2 : p2 = q2 <;> simp [Matrix.diagonal_apply, h2]
  · rw [dif_neg h, if_neg]
    intro heq; exact h (congrArg Sigma.fst heq)

end X6R15W

open X6R15W QAlgorithms.Papers.Independent.Renew46.P15 in
theorem solution {n r : ℕ} (s sPrime : GTTopRow n)
    (t : Fin r → GTTopRow n) (c : CGTable s sPrime t)
    (j : Fin r) (out : Pattern (t j)) (m : Pattern s) (mPrime : Pattern sPrime)
    (h : zWeight out ≠ zWeight m + zWeight mPrime) :
    c.coeff ⟨j, out⟩ (m, mPrime) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, zWeight out i ≠ zWeight m i + zWeight mPrime i := by
    by_contra hc
    push Not at hc
    exact h (funext fun i => by simpa using hc i)
  have hc := congrFun (congrFun (c.cartan i) ⟨j, out⟩) (m, mPrime)
  simp only [Matrix.mul_apply, zMatrix] at hc
  rw [Finset.sum_eq_single (m, mPrime)] at hc
  · rw [Finset.sum_eq_single ⟨j, out⟩] at hc
    · rw [tensor_diag, if_pos rfl, coupled_diag, if_pos rfl] at hc
      have : (zWeight out i - (zWeight m i + zWeight mPrime i)) * c.coeff ⟨j, out⟩ (m, mPrime) = 0 := by
        simp only at hc; linarith
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd (sub_eq_zero.1 h1) hi
      · exact h1
    · intro b _ hb
      rw [coupled_diag, if_neg (Ne.symm hb), zero_mul]
    · intro hb; exact absurd (Finset.mem_univ _) hb
  · intro b _ hb
    rw [tensor_diag, if_neg hb, mul_zero]
  · intro hb; exact absurd (Finset.mem_univ _) hb
