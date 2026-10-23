-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.clonedWheelSideInformation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:29:36.602554+00:00
-- url     : https://prove2.me/submissions/1cccafd0-9135-4b42-9ee5-dae2d548787d

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43
noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Renew46 QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

/-- Unnumbered cloned-wheel side-information example, PDF p.57. The second copy
may be consumed. A one-dimensional message and the identity recovery suffice for
A1 alone; recovery of both copies is deliberately not the task in this model. -/
theorem solution (n : ℕ) :
    ∃ T : Superop (Fin 1 × (Fin n → Fin 2)) (Fin n → Fin 2), IsChannel T ∧
      ∀ w : Fin n → Fin 4,
        T (Matrix.kronecker (1 : Matrix (Fin 1) (Fin 1) ℂ)
          (wordTensor (fun i => pureDensity (wheelVector (w i))))) =
          wordTensor (fun i => pureDensity (wheelVector (w i))) := by
  classical
  let K : Matrix (Fin n → Fin 2) (Fin 1 × (Fin n → Fin 2)) ℂ :=
    Matrix.of fun a p => if p.2 = a then 1 else 0
  refine ⟨krausApply (fun _ : Fin 1 => K), ⟨1, fun _ => K, ?_, fun _ => rfl⟩, ?_⟩
  · unfold IsKrausFamily
    ext p q
    rcases p with ⟨u, b⟩
    rcases q with ⟨u', b'⟩
    have hu : u = u' := Subsingleton.elim _ _
    subst hu
    simp [K, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Prod.ext_iff]
  · intro w
    ext a b
    simp [krausApply, K, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Fintype.sum_prod_type]

end
