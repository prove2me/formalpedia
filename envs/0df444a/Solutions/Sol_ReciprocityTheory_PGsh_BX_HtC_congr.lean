-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.HtC_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:26:07.906197+00:00
-- url     : https://prove2.me/submissions/b7be0a62-5535-4de6-8602-d56313b67900

import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulTensorEqZero

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
variable (B : BX R₀) {R : LAlg R₀} (Dp : DualPair R)
namespace ReciprocityTheory.PGsh.BX
theorem _root_.solution {N : ℕ} {y : B.G R} {x x' : B.G Dp.D} {E E' : (Dp.D : Type u)} (hx : x = x')
    (hE : E = E') : B.HtC Dp N y x E → B.HtC Dp N y x' E' := by
  subst hx hE
  exact id
end ReciprocityTheory.PGsh.BX
