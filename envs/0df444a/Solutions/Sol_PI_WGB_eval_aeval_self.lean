-- Prove2me | solution 1 for PI.WGB.eval_aeval_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:11.819212+00:00
-- url     : https://prove2.me/submissions/23b5ad5c-8daf-43c6-b09a-0488076e3ead

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)
namespace PI.WGB
theorem _root_.solution {σ : Type} (x : σ → ℂ) (g : σ → MvPolynomial σ ℂ) (p : MvPolynomial σ ℂ) :
    eval x (aeval g p) = eval (fun v => eval x (g v)) p := by
  rw [aeval_eq_bind₁]; exact eval₂Hom_bind₁ _ _ _ _
end PI.WGB
