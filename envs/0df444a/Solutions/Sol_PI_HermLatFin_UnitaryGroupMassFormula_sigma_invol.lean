-- Prove2me | solution 1 for PI.HermLatFin.UnitaryGroupMassFormula.sigma_invol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:28:49.87305+00:00
-- url     : https://prove2.me/submissions/4de27e10-4582-460b-8c29-fdd3d958a5eb

import Definitions.Def_Formalism_PeriodIntegrals_HermLatFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianLatticeFiniteness_HformTracePos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped ComplexOrder
noncomputable section
open PI PI.HermLatFin PI.HermLatFin.UnitaryGroupMassFormula
variable {E : Type} [Field E] [NumberField E]
namespace PI.HermLatFin.UnitaryGroupMassFormula
theorem _root_.solution (σ : E →+* E)
    (hσ : ∀ τ : E →+* ℂ, ∀ a : E, τ (σ a) = starRingEnd ℂ (τ a)) (a : E) : σ (σ a) = a := by
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply τ.injective
  rw [hσ, hσ, Complex.conj_conj]
end PI.HermLatFin.UnitaryGroupMassFormula
