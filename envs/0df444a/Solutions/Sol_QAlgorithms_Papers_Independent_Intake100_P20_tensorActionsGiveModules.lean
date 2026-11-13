-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P20.tensorActionsGiveModules
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-13T02:28:18.941197+00:00
-- url     : https://prove2.me/submissions/7c978a39-d4bd-4397-b899-f8e440c0c099

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intake100.P20


open CategoryTheory

open scoped TensorProduct

universe u v w z

/-- PDF p. 5: a tensor action makes the SAME abelian group a left module
 over the ring computed from the given monoid. Scalar multiplication is the
 given tensor map on pure tensors, so neither distributivity can be dropped. -/
theorem solution (M : ModuleCat.{0} ℤ) [MonObj M]
    (A : Type v) [AddCommGroup A] (n : TensorProduct ℤ M A →ₗ[ℤ] A)
    (h : TensorActionDiagrams M A n) :
    letI : Ring M := tensorRing M
    ∃ a : Module M A, ∀ r x, @SMul.smul M A a.toSMul r x = n (r ⊗ₜ[ℤ] x) := by
  letI : Ring M := tensorRing M
  refine ⟨{ smul := fun r x => n (r ⊗ₜ[ℤ] x)
            one_smul := h.1
            mul_smul := h.2
            smul_zero := fun r => by change n (r ⊗ₜ[ℤ] (0 : A)) = 0; simp
            smul_add := fun r x y => by change n (r ⊗ₜ[ℤ] (x+y)) = n (r ⊗ₜ[ℤ] x) + n (r ⊗ₜ[ℤ] y); simp [TensorProduct.tmul_add]
            zero_smul := fun x => by change n ((0 : M) ⊗ₜ[ℤ] x) = 0; erw [TensorProduct.zero_tmul, map_zero]
            add_smul := fun r s x => by change n ((r+s) ⊗ₜ[ℤ] x) = n (r ⊗ₜ[ℤ] x) + n (s ⊗ₜ[ℤ] x); erw [TensorProduct.add_tmul, map_add] },fun _ _ => rfl⟩
