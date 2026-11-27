-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.coordW_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:21:18.04907+00:00
-- url     : https://prove2.me/submissions/2ee2dbd7-c490-44e0-9251-440a42105147

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_L_f
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_e
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_f
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_of_isW


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
theorem _root_.solution (H : D.Hyp) {w : Fin r → n → A} (hw : ∀ a, IsW D (w a)) (s : Fin r → Fin r → A)
    (b : Fin r) : D.pW (D.L w s (D.f b)) = w b := by
  rw [L_f H]
  simp [pW_f H, pW_of_isW (hw b), pW_e H]
end PI.VolSemiDirect.W.PG.Dat
