-- Prove2me | solution 1 for PI.FoldMult.UnitaryGroupMassFormula.one_le_mult
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:01.546974+00:00
-- url     : https://prove2.me/submissions/a5bf1471-b0ba-42ac-b2b2-406333891fbb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FoldMult
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MultiplicityMeasurability_MeasurableMult

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
theorem _root_.solution (Γ : Subgroup G) (Ω : Set G) (h1 : (1 : G) ∈ Ω) (x : G) :
    1 ≤ Formalism.L2.SG.FoldBound.mult Γ Ω x := by
  unfold Formalism.L2.SG.FoldBound.mult
  refine le_iSup_of_le x ?_
  have h : (1 : ℕ∞) ≤ ({γ : Γ | x⁻¹ * ((γ : G) * x) ∈ Ω} : Set Γ).encard :=
    Set.one_le_encard_iff_nonempty.2 ⟨1, by simpa using h1⟩
  exact_mod_cast h
end PI.FoldMult.UnitaryGroupMassFormula
