-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.h_W_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:50:02.464+00:00
-- url     : https://prove2.me/submissions/5495a384-faa0-4bfa-905f-7776bc46521a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_symm


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
namespace PI.VolSemiDirect.W.PG.Dat
theorem _root_.solution (H : D.Hyp) {w : n → A} (hw : IsW D w) (a : Fin r) : D.h w (D.e a) = 0 := by
  rw [h_symm H (D.e a) w, hw.1 a, map_zero]
end PI.VolSemiDirect.W.PG.Dat
