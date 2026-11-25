-- Prove2me | solution 1 for PI.PoincareSeriesFinite.UnitaryGroupMassFormula.quotientLIntegral_le_multiplicityLIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:03:40.269096+00:00
-- url     : https://prove2.me/submissions/40d98979-3d54-45b8-a1a9-030571a94520

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_FoldBound
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_PoincareSeriesSquareIntegrable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MultiplicityMeasurability_MeasurableMult
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientIntegralBound_QuotientLIntegralLeMultiplicityLIntegral
import Theorems.Thm_PI_FoldMult_UnitaryGroupMassFormula_one_le_mult


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
open PI PI.PoincareSeriesFinite PI.PoincareSeriesFinite.UnitaryGroupMassFormula
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable
namespace PI.PoincareSeriesFinite.UnitaryGroupMassFormula
theorem _root_.solution {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [MeasurableSpace G] (μ : Measure G) (Γ : Subgroup G) (Ω : Set G)
    (h1 : (1 : G) ∈ Ω) (F : Set G) (Ph : G → ℂ) :
    quotientLIntegral μ F Ph ≤ multiplicityLIntegral μ Γ Ω F Ph := by
  unfold quotientLIntegral multiplicityLIntegral
  refine lintegral_mono fun y => ?_
  calc ‖Ph y‖ₑ = 1 * ‖Ph y‖ₑ := (one_mul _).symm
    _ ≤ mult Γ Ω y * ‖Ph y‖ₑ := by
      gcongr
      exact PI.FoldMult.UnitaryGroupMassFormula.one_le_mult Γ Ω h1 y
end PI.PoincareSeriesFinite.UnitaryGroupMassFormula
