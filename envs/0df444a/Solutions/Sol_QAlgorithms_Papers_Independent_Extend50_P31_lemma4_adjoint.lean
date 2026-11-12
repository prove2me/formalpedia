-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.lemma4_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T00:04:54.722622+00:00
-- url     : https://prove2.me/submissions/9e61f982-8e3b-4fe3-9069-c3699bb7863c

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

open QAlgorithms.Papers.Independent.Extend50.P31 in
theorem solution (n : ℕ) (hn : 0 < n) (Phi : EndMat n) :
    rowMatrixRepresentative (hsAdjoint Phi) = (rowMatrixRepresentative Phi)ᴴ := by
  ext p q
  show (hsAdjoint Phi) (matrixUnit q.1 q.2) p.1 p.2 = star (Phi (matrixUnit p.1 p.2) q.1 q.2)
  show (∑ i, ∑ j, _ * matrixUnit q.1 q.2 i j) = star (Phi (matrixUnit p.1 p.2) q.1 q.2)
  have hz : ∀ i j, (i ≠ q.1 ∨ j ≠ q.2) → matrixUnit q.1 q.2 i j = 0 := by
    intro i j h
    unfold matrixUnit
    rcases h with h | h
    · simp [Matrix.single_apply, h, Ne.symm h]
    · simp [Matrix.single_apply, h, Ne.symm h]
  have h1 : matrixUnit q.1 q.2 q.1 q.2 = 1 := by
    unfold matrixUnit
    simp
  rw [Finset.sum_eq_single q.1
      (fun i _ hi => Finset.sum_eq_zero (fun j _ => by rw [hz i j (Or.inl hi), mul_zero]))
      (fun h => absurd (Finset.mem_univ _) h),
    Finset.sum_eq_single q.2 (fun j _ hj => by rw [hz q.1 j (Or.inr hj), mul_zero])
      (fun h => absurd (Finset.mem_univ _) h),
    h1, mul_one]
  first
  | rfl
  | (change star _ = star _; congr)

end
