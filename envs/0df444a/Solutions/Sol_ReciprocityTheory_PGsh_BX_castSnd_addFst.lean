-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.castSnd_addFst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:47:28.583948+00:00
-- url     : https://prove2.me/submissions/880f2a3e-2dce-49a2-a093-4734313c1e92

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
theorem _root_.solution {x x' y y' : B.G R} (h : y = y') (u : B.P R x y) (u' : B.P R x' y) :
    B.tr2 h (B.add1 u u') = B.add1 (B.tr2 h u) (B.tr2 h u') := by
  subst h
  rfl
end ReciprocityTheory.PGsh.BX
