-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.coordK_lTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:21:05.54073+00:00
-- url     : https://prove2.me/submissions/441902dd-e38b-4fe5-868c-a92787437b76

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
theorem _root_.solution {M M' : Type u} [AddCommGroup M] [Module R₀ M] [AddCommGroup M'] [Module R₀ M']
    (f : M →ₗ[R₀] M') (k : Module.Free.ChooseBasisIndex R₀ B.gg) (x : B.gg ⊗[R₀] M) :
    B.coordK M' k (LinearMap.lTensor B.gg f x) = f (B.coordK M k x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul g m => simp [coordK]
  | add x y hx hy => simp only [map_add, hx, hy]
end ReciprocityTheory.PGsh.BX
