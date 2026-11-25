-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.exists_lim_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:52:25.449639+00:00
-- url     : https://prove2.me/submissions/42a3169a-b4b6-43dd-a5e0-b12c5cb98c14

import Definitions.Def_ReciprocityTheory_DualLattices_NsmulKerZero
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsLimTensor
import Theorems.Thm_ReciprocityTheory_PGsh_BX_coordK_lTensor
import Theorems.Thm_ReciprocityTheory_PGsh_BX_sum_coordK

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
theorem _root_.solution (Tw : ATowerL R₀ p) (wb : ∀ n, B.gg ⊗[R₀] (Tw.R n : Type u))
    (hwb : ∀ n, LinearMap.lTensor B.gg (Tw.r n).1.toLinearMap (wb (n + 1)) = wb n) :
    ∃ bt : B.gg ⊗[R₀] (Tw.O : Type u), ∀ n, LinearMap.lTensor B.gg (Tw.q n).1.toLinearMap bt = wb n := by
  choose a ha using fun k => Tw.complete (fun n => B.coordK (Tw.R n) k (wb n)) (fun n => by
    rw [← hwb n, B.coordK_lTensor]
    rfl)
  refine ⟨∑ k, (Module.Free.chooseBasis R₀ B.gg k) ⊗ₜ[R₀] a k, fun n => ?_⟩
  rw [map_sum]
  simp only [LinearMap.lTensor_tmul]
  conv_rhs => rw [← B.sum_coordK _ (wb n)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← ha k n]
  rfl
end ReciprocityTheory.PGsh.BX
