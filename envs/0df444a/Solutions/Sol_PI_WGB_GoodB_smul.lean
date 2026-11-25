-- Prove2me | solution 1 for PI.WGB.GoodB_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:54.383799+00:00
-- url     : https://prove2.me/submissions/4a302773-9253-40b9-87cd-d8de367d0521

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB

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
open Formalism.BasicNotions MvPolynomial
variable {σ : Type*} (R : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ) (ψ : σ → ℕ)
namespace PI.WGB
theorem _root_.solution (c : ℂ) {p : MvPolynomial σ ℂ} {d : ℕ} (hp : GoodB R ψ p d) : GoodB R ψ (c • p) d := by
  refine ⟨Submodule.smul_mem _ c hp.1, ?_⟩
  rw [map_smul, ← smul_sub]
  exact Submodule.smul_mem _ c hp.2
end PI.WGB
