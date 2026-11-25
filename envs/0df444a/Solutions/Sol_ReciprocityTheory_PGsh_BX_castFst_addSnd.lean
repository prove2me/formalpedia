-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.castFst_addSnd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:31:09.366995+00:00
-- url     : https://prove2.me/submissions/0d1ab626-13b4-4d81-a12e-f2c0493c9123

import Definitions.Def_ReciprocityTheory_DualLattices_SeriesState
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulFstAddSnd
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {R : LAlg R₀}
namespace ReciprocityTheory.PGsh.BX
theorem _root_.solution {x x' y y' : B.G R} (h : x = x') (u : B.P R x y) (u' : B.P R x y') :
    B.tr1 h (B.add2 u u') = B.add2 (B.tr1 h u) (B.tr1 h u') := by
  subst h
  rfl
end ReciprocityTheory.PGsh.BX
