-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.swap_castSnd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:38:10.744453+00:00
-- url     : https://prove2.me/submissions/1e06b61f-7099-49e9-a6ed-5879c29097ac

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
theorem _root_.solution {x y y' : B.G R} (h : y = y') (u : B.P R x y) :
    B.sw (B.tr2 h u) = B.tr1 h (B.sw u) := by
  subst h
  rfl
end ReciprocityTheory.PGsh.BX
