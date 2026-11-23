-- Prove2me | solution 1 for ReciprocityTheory.PGsh.hext_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:10.122564+00:00
-- url     : https://prove2.me/submissions/e0ba50b4-309e-44c9-9180-39c46a6f27c1

import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan

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
theorem _root_.solution (B : BX R₀) {R : LAlg R₀} (h : B.gg →ₗ[R₀] (R : Type u)) (w : B.gg) (r : (R : Type u)) :
    hext B h (w ⊗ₜ r) = h w * r := by
  simp [hext]
end ReciprocityTheory.PGsh
