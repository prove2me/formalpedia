-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.h_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:18:15.669445+00:00
-- url     : https://prove2.me/submissions/40878600-d61b-467d-aa15-bd04147ca5dd

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
theorem _root_.solution (x y : n → A) (c : A) : D.h x (c • y) = c * D.h x y := by
  simpa only [hL_apply, smul_eq_mul] using (D.hL x).map_smul c y
end PI.VolSemiDirect.W.PG.Dat
