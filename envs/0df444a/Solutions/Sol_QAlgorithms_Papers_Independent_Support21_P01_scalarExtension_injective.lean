-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P01.scalarExtension_injective
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:00:08.141767+00:00
-- url     : https://prove2.me/submissions/0236ae68-2e6b-436f-a477-35f520f321b1

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P01
noncomputable section

open scoped TensorProduct

open QAlgorithms.Papers.Independent.Support21.P01

open QAlgorithms.Papers.Independent.Renew46.P16

/-- Lemma 2.20, PDF p.15: the canonical fraction-field scalar-extension map
is injective for every free module, with no finite-rank assumption. -/
theorem solution
    (R F M : Type*) [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F]
    [AddCommGroup M] [Module R M] [Module.Free R M] :
    Function.Injective (fun x : M => TensorProduct.tmul R x (1 : F)) := by
  have hinj : Function.Injective (Algebra.linearMap R F) := IsFractionRing.injective R F
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := M) (Algebra.linearMap R F) hinj
  have e : (fun x : M => TensorProduct.tmul R x (1 : F)) =
      (LinearMap.lTensor M (Algebra.linearMap R F)) ∘ (TensorProduct.rid R M).symm := by
    funext x; simp
  rw [e]
  exact h.comp (TensorProduct.rid R M).symm.injective


end
