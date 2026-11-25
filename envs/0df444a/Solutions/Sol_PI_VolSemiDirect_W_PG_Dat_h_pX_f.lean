-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.h_pX_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:50:23.103753+00:00
-- url     : https://prove2.me/submissions/04f1c5c8-b81f-4d18-a481-016a58555663

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_smul_left
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_sum_left
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pX_apply


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
variable {D : Dat A n r}
namespace PI.VolSemiDirect.W.PG.Dat
theorem _root_.solution (H : D.Hyp) (b : Fin r) (u : n → A) :
    D.h (D.pX u) (D.f b) = D.σA (D.h (D.f b) u) := by
  rw [pX_apply, h_sum_left]
  simp [h_smul_left, H.ef]
end PI.VolSemiDirect.W.PG.Dat
