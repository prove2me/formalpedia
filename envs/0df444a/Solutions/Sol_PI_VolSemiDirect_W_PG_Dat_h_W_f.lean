-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.h_W_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:50:06.00302+00:00
-- url     : https://prove2.me/submissions/64097c5a-132d-408e-b2b6-f490987d3490

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
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
variable {D : Dat A n r}
namespace PI.VolSemiDirect.W.PG.Dat
theorem _root_.solution (H : D.Hyp) {w : n → A} (hw : IsW D w) (b : Fin r) : D.h w (D.f b) = 0 := by
  have hw' : (∀ c, D.h (D.e c) w = 0) ∧ (∀ c, D.h (D.f c) w = 0) ∧ D.h D.z w = 0 := hw
  rw [h_symm H, hw'.2.1 b, map_zero]
end PI.VolSemiDirect.W.PG.Dat
