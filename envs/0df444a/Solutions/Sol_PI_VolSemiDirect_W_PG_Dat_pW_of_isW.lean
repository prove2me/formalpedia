-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.pW_of_isW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:34:38.587161+00:00
-- url     : https://prove2.me/submissions/7f754fb0-1c08-4173-a97c-4f774178c5b7

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_apply
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
theorem _root_.solution {w : n → A} (hw : IsW D w) : D.pW w = w := by
  rw [pW_apply, pU_of_isW hw, sub_zero]
end PI.VolSemiDirect.W.PG.Dat
