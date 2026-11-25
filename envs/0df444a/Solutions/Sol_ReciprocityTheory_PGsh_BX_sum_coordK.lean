-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.sum_coordK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:32:37.209399+00:00
-- url     : https://prove2.me/submissions/ac1b96ca-cfcb-48b1-86e2-3140d5cc80bb

import Definitions.Def_ReciprocityTheory_DualLattices_NsmulKerZero
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsLimTensor

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
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {p : ℕ}
namespace ReciprocityTheory.PGsh.BX
theorem _root_.solution (M : Type u) [AddCommGroup M] [Module R₀ M] (x : B.gg ⊗[R₀] M) :
    ∑ k, (Module.Free.chooseBasis R₀ B.gg k) ⊗ₜ[R₀] B.coordK M k x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul g m =>
    simp only [coordK, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
      TensorProduct.lid_tmul, Module.Basis.coord_apply]
    simp_rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    rw [← TensorProduct.sum_tmul, Module.Basis.sum_repr]
  | add x y hx hy =>
    simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]
end ReciprocityTheory.PGsh.BX
