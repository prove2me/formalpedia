-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P16.rationalSystem_flat
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:14:05.343801+00:00
-- url     : https://prove2.me/submissions/097300df-faf0-4bb5-bf1a-46635cee253b

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16
noncomputable section

universe u

open QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section Pairings

variable {R A P Q B M : Type u} [CommRing R]

variable [AddCommGroup A] [Module R A] [AddCommGroup P] [Module R P]

variable [AddCommGroup Q] [Module R Q] [AddCommGroup B] [Module R B]

variable [AddCommGroup M] [Module R M]

theorem g74b_alpha_rTensor {R A P N N' : Type u} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (b : P →ₗ[R] A →ₗ[R] R) (f : N →ₗ[R] N') (x : N ⊗[R] P) (a : A) :
    pairingAlpha b N' (f.rTensor P x) a = f (pairingAlpha b N x a) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul n p =>
    change b p a • f n = f (b p a • n)
    rw [map_smul]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- Remark 2.4, PDF p.4: rational systems have flat first module. -/
theorem solution (b : P →ₗ[R] A →ₗ[R] R) (h : IsRationalSystem b) :
    Module.Flat R P := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap']
  intro N N' _ _ _ _ f hf x y hxy
  apply h N
  ext a
  apply hf
  rw [← g74b_alpha_rTensor, ← g74b_alpha_rTensor, hxy]


end Pairings



end
