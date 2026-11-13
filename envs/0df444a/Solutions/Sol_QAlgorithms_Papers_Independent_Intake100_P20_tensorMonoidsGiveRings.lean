-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P20.tensorMonoidsGiveRings
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-13T02:27:11.194205+00:00
-- url     : https://prove2.me/submissions/571e1713-a096-4930-8e94-3ae071fb3f01

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intake100.P20


open CategoryTheory

open scoped TensorProduct

universe u v w z

/-- PDF p. 5: a tensor monoid in Ab gives a ring with its original addition,
unit e(1), and multiplication m(x tensor y). The zero ring is allowed. -/
theorem solution (M : ModuleCat.{0} ℤ) [MonObj M] :
    let originalAddition : AddCommGroup M := inferInstance
    let tensorMultiplication : M → M → M :=
      fun x y => MonObj.mul (X := M) (x ⊗ₜ[ℤ] y)
    ∃ r : Ring M,
      r = tensorRing M ∧ r.toAddCommGroup = originalAddition ∧
      r.one = MonObj.one (X := M) (1 : ℤ) ∧
      (∀ x y : M, r.mul x y = tensorMultiplication x y) := by
  exact ⟨tensorRing M,rfl,rfl,rfl,fun _ _ => rfl⟩
