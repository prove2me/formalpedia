-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P01.scalarExtension_submodule_injective
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:00:18.744357+00:00
-- url     : https://prove2.me/submissions/df58414d-0ab3-4d1a-bd7d-ce0a6d58fbfa

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P01
noncomputable section

open scoped TensorProduct

open QAlgorithms.Papers.Independent.Support21.P01

open QAlgorithms.Papers.Independent.Renew46.P16

/-- Lemma 2.21, PDF p.15: tensor the actual submodule inclusion with id_F.
Only the ambient module N2 is assumed free; N1 need not be free or finite. -/
theorem solution
    (R F N2 : Type*) [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F]
    [AddCommGroup N2] [Module R N2] [Module.Free R N2]
    (N1 : Submodule R N2) :
    Function.Injective
      (TensorProduct.map N1.subtype (LinearMap.id : F →ₗ[R] F)) := by
  have : Module.Flat R F := IsLocalization.flat F (nonZeroDivisors R)
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := F) N1.subtype Subtype.val_injective


end
