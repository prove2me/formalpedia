-- Prove2me | solution 1 for PI.VolStabSW.sigma_invol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:01:09.77053+00:00
-- url     : https://prove2.me/submissions/9fef0838-f6d1-4fb2-85c5-b0976eded596

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace PI.VolStabSW
theorem _root_.solution [NumberField E] (σ : E →ₐ[F] E)
    (hσ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  exact τ.injective (by rw [hσ τ, hσ τ, star_star])
end PI.VolStabSW
