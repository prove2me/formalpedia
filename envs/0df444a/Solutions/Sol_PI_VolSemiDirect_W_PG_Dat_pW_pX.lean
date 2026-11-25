-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.pW_pX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:50:02.21127+00:00
-- url     : https://prove2.me/submissions/424795a6-95fe-4c00-8241-64cf6196476c

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pX_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_e

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
theorem _root_.solution (H : D.Hyp) (u : n → A) : D.pW (D.pX u) = 0 := by
  rw [pX_apply]
  simp [map_sum, map_smul, pW_e H]
end PI.VolSemiDirect.W.PG.Dat
