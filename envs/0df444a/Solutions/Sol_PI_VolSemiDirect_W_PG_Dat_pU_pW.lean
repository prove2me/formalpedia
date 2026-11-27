-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.pU_pW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:21:20.368902+00:00
-- url     : https://prove2.me/submissions/8eae81b4-7590-44ef-977a-c7337f0c3055

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_isW_pW
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pU_of_isW

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.VolSemiDirect.W.PG.Dat
variable (D : Dat A n r)
variable {D}
variable (D)
variable {D}
namespace PI.VolSemiDirect.W.PG.Dat
theorem _root_.solution (H : D.Hyp) (v : n → A) : D.pU (D.pW v) = 0 := pU_of_isW (isW_pW H v)
end PI.VolSemiDirect.W.PG.Dat
