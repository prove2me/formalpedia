-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.L_fixEZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:20:08.723433+00:00
-- url     : https://prove2.me/submissions/f557ed84-755c-4154-85f0-b5920ff84691

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_L_e
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_reflection_fixes_normal

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
theorem _root_.solution (H : D.Hyp) (w : Fin r → n → A) (s : Fin r → Fin r → A) : D.FixEZ (D.L w s) := by
  show (∀ a, _ = _) ∧ _ = _
  exact ⟨fun a => L_e H w s a, reflection_fixes_normal H w s⟩
end PI.VolSemiDirect.W.PG.Dat
