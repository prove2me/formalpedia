-- Prove2me | solution 1 for P2M_PI_VolSemiDirect_W_PG_Dat_N_f__c785d52daa49
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:50:18.46691+00:00
-- url     : https://prove2.me/submissions/d8e4a324-db03-44ef-b5cf-da01b740c02b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_N_f
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
theorem _root_.solution (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hU : D.Uni S) (b : Fin r) :
    S (D.f b) = D.f b + D.pW (S (D.f b)) + D.pX (S (D.f b)) := by
  rw [pX_apply]
  exact N_f H hS hU b
end PI.VolSemiDirect.W.PG.Dat
