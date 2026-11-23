-- Prove2me | solution 1 for PI.FoldMult.UnitaryGroupMassFormula.mult_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:12.938805+00:00
-- url     : https://prove2.me/submissions/d6c0611b-1dcd-402d-9098-35404f2bb3c5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FoldMult
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MultiplicityMeasurability_MeasurableMult
import Theorems.Thm_PI_FoldMult_UnitaryGroupMassFormula_cnt_encard_le

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
theorem _root_.solution (Γ : Subgroup G) [DiscreteTopology Γ] (Ω : Set G) (hΩ : IsCompact Ω)
    (x : G) : Formalism.L2.SG.FoldBound.mult Γ Ω x < ⊤ := by
  obtain ⟨N, hN, hle⟩ := cnt_encard_le Γ Ω hΩ x
  exact lt_of_le_of_lt (b := (N : ℝ≥0∞)) (iSup_le fun y => ENat.toENNReal_le.2 (hle y))
    (ENat.toENNReal_lt_top.2 hN)
end PI.FoldMult.UnitaryGroupMassFormula
