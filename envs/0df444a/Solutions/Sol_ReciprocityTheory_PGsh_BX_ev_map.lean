-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.ev_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:21:08.833773+00:00
-- url     : https://prove2.me/submissions/33146462-89e0-48ab-ad24-1b68fa7add24

import Definitions.Def_ReciprocityTheory_DualLattices_NsetExpInjectiveSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_OneAddPowOfSq

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
namespace ReciprocityTheory.PGsh
namespace BX
theorem _root_.solution (B : BX R₀) {R S : LAlg R₀} (f : (R : Type u) →ₐ[R₀] (S : Type u))
    (h : B.gg →ₗ[R₀] (R : Type u)) (v : B.gg ⊗[R₀] (R : Type u)) :
    f (B.ev h v) = B.ev (f.toLinearMap ∘ₗ h) (LinearMap.lTensor B.gg f.toLinearMap v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp [BX.ev]
  | tmul g r => simp [BX.ev]
  | add a b ha hb =>
    simp only [BX.ev, map_add] at ha hb ⊢
    rw [ha, hb]
end BX
end ReciprocityTheory.PGsh
