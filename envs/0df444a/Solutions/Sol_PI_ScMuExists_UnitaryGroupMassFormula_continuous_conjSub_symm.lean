-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.continuous_conjSub_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:19:01.335488+00:00
-- url     : https://prove2.me/submissions/74eafc43-45ef-4e23-b494-0ab09bb10b70

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
    (h2 : ∀ x ∈ N, g⁻¹ * x * g ∈ N) : Continuous (conjSub N g h1 h2).symm := by
  show Continuous fun x : N => (⟨g⁻¹ * x * g, h2 x x.2⟩ : N)
  exact Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
end PI.ScMuExists.UnitaryGroupMassFormula
