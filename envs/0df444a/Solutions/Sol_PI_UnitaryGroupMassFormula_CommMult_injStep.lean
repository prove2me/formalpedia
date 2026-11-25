-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CommMult.injStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:38:38.502521+00:00
-- url     : https://prove2.me/submissions/82574165-ae1c-4cb7-ac0f-58ef90fe9432

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CommutingMultiplicity_SchurStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CommutingMultiplicity_InjStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CommMult
open Matrix
namespace PI.UnitaryGroupMassFormula.CommMult
theorem _root_.solution : InjStep := by
  intro G _ N M π σ hirr T hT hne
  have hstab : ∀ g, ∀ v ∈ LinearMap.ker (Matrix.toLin' T),
      ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ).mulVec v ∈ LinearMap.ker (Matrix.toLin' T) := by
    intro g v hv
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, ← hT g, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  rcases hirr _ hstab with h | h
  · obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' T) h
    refine ⟨LinearMap.toMatrix' g, ?_⟩
    calc LinearMap.toMatrix' g * T = LinearMap.toMatrix' g * LinearMap.toMatrix' (Matrix.toLin' T) := by
          rw [LinearMap.toMatrix'_toLin']
      _ = LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' T) := (LinearMap.toMatrix'_comp _ _).symm
      _ = 1 := by rw [hg, LinearMap.toMatrix'_id]
  · have h0 : Matrix.toLin' T = 0 := LinearMap.ker_eq_top.mp h
    exact absurd (Matrix.toLin'.injective (h0.trans (map_zero _).symm)) hne
end PI.UnitaryGroupMassFormula.CommMult
