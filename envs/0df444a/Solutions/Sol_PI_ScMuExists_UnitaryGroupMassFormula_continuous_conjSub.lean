-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.continuous_conjSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:36:42.285988+00:00
-- url     : https://prove2.me/submissions/d83f8c50-7912-4ea8-98e6-ff71cd603203

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ModOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal Pointwise
noncomputable section
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution (N : Subgroup G) (g : G) (h1 : ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (h2 : ∀ x ∈ N, g⁻¹ * x * g ∈ N) : Continuous (conjSub N g h1 h2) := by
  show Continuous fun x : N => (⟨g * x * g⁻¹, h1 x x.2⟩ : N)
  exact Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
end PI.ScMuExists.UnitaryGroupMassFormula
