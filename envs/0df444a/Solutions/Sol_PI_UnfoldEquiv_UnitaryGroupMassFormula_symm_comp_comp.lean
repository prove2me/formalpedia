-- Prove2me | solution 1 for PI.UnfoldEquiv.UnitaryGroupMassFormula.symm_comp_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:33:10.706633+00:00
-- url     : https://prove2.me/submissions/d9a38c18-c022-48f5-be3f-eb918da54d3a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_Points
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_CompSymmComp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI.UnfoldEquiv PI.UnfoldEquiv.Loc
noncomputable section
open PI PI.UnfoldEquiv PI.UnfoldEquiv.UnitaryGroupMassFormula
variable {k : Type} [CommRing k]
namespace PI.UnfoldEquiv.UnitaryGroupMassFormula
theorem _root_.solution {n' n c : ℕ} (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))
    (y : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)) : r.symm.toLinearMap ∘ₗ (r.toLinearMap ∘ₗ y) = y := by
  apply LinearMap.ext
  intro v
  simp
end PI.UnfoldEquiv.UnitaryGroupMassFormula
