-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P16.tensor_rationalSystem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:15:44.160365+00:00
-- url     : https://prove2.me/submissions/1d5df8ad-5dcc-4a1c-b7fd-e740490b467d

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

theorem g74b_tensor_key {R A P Q B X : Type u} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] [AddCommGroup B] [Module R B]
    [AddCommGroup X] [Module R X]
    (b : P →ₗ[R] A →ₗ[R] R) (c : Q →ₗ[R] B →ₗ[R] R) (z : X ⊗[R] (P ⊗[R] Q)) (a : A) (d : B) :
    pairingAlpha (tensorPairing b c) X z (a ⊗ₜ[R] d) =
      pairingAlpha c X (pairingAlpha b (X ⊗[R] Q)
        (TensorProduct.rightComm R X P Q ((TensorProduct.assoc R X P Q).symm z)) a) d := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x w =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul p q =>
      change (b p a * c q d) • x = c q d • (b p a • x)
      rw [smul_smul, mul_comm]
    | add w w' hw hw' =>
      simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply] at hw hw' ⊢
      rw [hw, hw']
  | add z z' hz hz' =>
    simp only [map_add, LinearMap.add_apply] at hz hz' ⊢
    rw [hz, hz']

/-- Proposition 2.5, PDF pp.4-5: tensoring rational systems. -/
theorem solution (b : P →ₗ[R] A →ₗ[R] R)
    (c : Q →ₗ[R] B →ₗ[R] R) (hb : IsRationalSystem b) (hc : IsRationalSystem c) :
    IsRationalSystem (tensorPairing b c) := by
  intro X _ _ z z' hzz
  have e_inj : Function.Injective (fun z : X ⊗[R] (P ⊗[R] Q) =>
      TensorProduct.rightComm R X P Q ((TensorProduct.assoc R X P Q).symm z)) :=
    (TensorProduct.rightComm R X P Q).injective.comp (TensorProduct.assoc R X P Q).symm.injective
  apply e_inj
  apply hb (X ⊗[R] Q)
  ext a
  apply hc X
  ext d
  rw [← g74b_tensor_key, ← g74b_tensor_key, hzz]


end Pairings



end
