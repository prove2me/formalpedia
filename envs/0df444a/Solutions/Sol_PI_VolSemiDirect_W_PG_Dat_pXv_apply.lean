-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.pXv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:18:09.781475+00:00
-- url     : https://prove2.me/submissions/a6f17b6c-19e7-4dac-bbab-b6bad897ac0c

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
variable {D}
variable (D)
namespace PI.VolSemiDirect.W.PG.Dat
theorem _root_.solution (v : n → A) : D.pXv v = ∑ a, D.h (D.e a) v • D.f a := by
  simp only [pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, hL_apply]
end PI.VolSemiDirect.W.PG.Dat
