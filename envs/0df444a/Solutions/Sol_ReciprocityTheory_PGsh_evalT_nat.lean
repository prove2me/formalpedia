-- Prove2me | solution 1 for ReciprocityTheory.PGsh.evalT_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:47:28.562922+00:00
-- url     : https://prove2.me/submissions/ddbec205-a1ae-4759-8949-5db856387dc9

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
import Theorems.Thm_ReciprocityTheory_PGsh_evalT_tmul
import Theorems.Thm_ReciprocityTheory_PGsh_evalT_add
import Theorems.Thm_ReciprocityTheory_PGsh_evalT_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
variable {M : Type u} [AddCommGroup M] [Module R₀ M]
namespace ReciprocityTheory.PGsh
theorem _root_.solution {A C : Type u} [CommRing A] [Algebra R₀ A] [CommRing C] [Algebra R₀ C]
    (ρ : A →ₐ[R₀] C) (H : M →ₗ[R₀] A) (K : Submodule R₀ A) (K' : Submodule R₀ C)
    (hK : ∀ a ∈ K, ρ.toLinearMap a ∈ K') (Y : M ⊗[R₀] K) :
    ρ (evalT H K Y) = evalT (ρ.toLinearMap ∘ₗ H) K' (LinearMap.lTensor M (ρ.toLinearMap.restrict hK) Y) := by
  induction Y using TensorProduct.induction_on with
  | zero => simp only [evalT_zero, map_zero]
  | tmul g k =>
    rw [evalT_tmul, LinearMap.lTensor_tmul, evalT_tmul, map_mul]
    rfl
  | add Y Y' hY hY' => rw [evalT_add, map_add, hY, hY', map_add, evalT_add]
end ReciprocityTheory.PGsh
