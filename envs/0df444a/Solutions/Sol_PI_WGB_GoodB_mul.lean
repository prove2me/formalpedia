-- Prove2me | solution 1 for PI.WGB.GoodB_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:32:44.089349+00:00
-- url     : https://prove2.me/submissions/89c4212f-dd4b-40c1-8e71-dc6cd6d9c140

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB
import Theorems.Thm_PI_WGB_FiltB_mono
import Theorems.Thm_PI_WGB_FiltB_mul

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
theorem _root_.solution {p q : MvPolynomial σ ℂ} {d d' : ℕ} (hp : GoodB R ψ p d) (hq : GoodB R ψ q d') :
    GoodB R ψ (p * q) (d + d') := by
  refine ⟨FiltB_mul ψ hp.1 hq.1, ?_⟩
  have hRq : R q ∈ FiltB ψ d' := by
    have e : R q = (R q - q) + q := by ring
    rw [e]
    exact Submodule.add_mem _ (FiltB_mono ψ (Nat.le_succ d') hq.2) hq.1
  have e : R (p * q) - p * q = (R p - p) * R q + p * (R q - q) := by
    rw [map_mul]; ring
  rw [e]
  refine Submodule.add_mem _ ?_ ?_
  · have := FiltB_mul ψ hp.2 hRq
    rwa [show d + 1 + d' = d + d' + 1 by ring] at this
  · have := FiltB_mul ψ hp.1 hq.2
    rwa [show d + (d' + 1) = d + d' + 1 by ring] at this
end PI.WGB
