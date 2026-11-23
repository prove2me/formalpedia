-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.h_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:34:29.544797+00:00
-- url     : https://prove2.me/submissions/8dc5dbf2-b024-4542-a2ee-19950e8c25a8

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_hL_apply

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
namespace PI.VolSemiDirect.W.PG.Dat
theorem _root_.solution (x y y' : n → A) : D.h x (y - y') = D.h x y - D.h x y' := by
  simpa only [hL_apply] using (D.hL x).map_sub y y'
end PI.VolSemiDirect.W.PG.Dat
