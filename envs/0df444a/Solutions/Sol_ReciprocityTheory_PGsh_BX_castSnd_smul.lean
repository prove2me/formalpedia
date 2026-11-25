-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.castSnd_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:42:50.086947+00:00
-- url     : https://prove2.me/submissions/33703933-5c4b-4755-846e-7158331c8a4b

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
theorem _root_.solution {a b x : B.G R} (h : a = b) (l : (R : Type u)ˣ) (u : B.P R x a) :
    B.tr2 h (B.smul l u) = B.smul l (B.tr2 h u) := by
  subst h
  rfl
end ReciprocityTheory.PGsh.BX
