-- Prove2me | solution 1 for PI.FoldMult.UnitaryGroupMassFormula.measurable_mult
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:47:17.900013+00:00
-- url     : https://prove2.me/submissions/2f62d986-0c81-4345-85ec-bdffa7297f44

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FoldMult
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MultiplicityMeasurability_MeasurableMult
import Theorems.Thm_PI_FoldMult_UnitaryGroupMassFormula_isClosed_hitSet
import Theorems.Thm_PI_FoldMult_UnitaryGroupMassFormula_mult_eq_iSup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
open PI PI.FoldMult PI.FoldMult.UnitaryGroupMassFormula
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
namespace PI.FoldMult.UnitaryGroupMassFormula
theorem _root_.solution [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (Ω : Set G) (hΩ : IsCompact Ω) :
    Measurable (Formalism.L2.SG.FoldBound.mult Γ Ω) := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hm : Formalism.L2.SG.FoldBound.mult Γ Ω =
      fun x => ⨆ A : Finset Γ, (hitSet Γ Ω A).indicator (fun _ => (A.card : ℝ≥0∞)) x :=
    funext (mult_eq_iSup Γ Ω hΩ)
  rw [hm]
  exact Measurable.iSup fun A => measurable_const.indicator (isClosed_hitSet Γ Ω hΩ A).measurableSet
end PI.FoldMult.UnitaryGroupMassFormula
