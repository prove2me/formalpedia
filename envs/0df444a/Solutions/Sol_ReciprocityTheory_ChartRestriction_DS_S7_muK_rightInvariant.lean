-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.muK_rightInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:14:44.590801+00:00
-- url     : https://prove2.me/submissions/dec40872-f691-4ed6-8e51-62288fc67bbf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFactsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_compactSpace_KG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (ε : Fin n → Bool) : (muK ε).IsMulRightInvariant := by
  have := compactSpace_KG ε
  refine ⟨fun k => ?_⟩
  set ν := Measure.map (fun x => x * k) (muK ε) with hν
  have : IsFiniteMeasure (muK ε) := ⟨isCompact_univ.measure_lt_top⟩
  have : IsFiniteMeasure ν := Measure.isFiniteMeasure_map _ _
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace ν (muK ε)
  have hu : ν Set.univ = muK ε Set.univ := by
    rw [hν, Measure.map_apply (measurable_mul_const k) MeasurableSet.univ, Set.preimage_univ]
  have hpos : muK ε Set.univ ≠ 0 := (isOpen_univ.measure_pos (muK ε) Set.univ_nonempty).ne'
  have htop : muK ε Set.univ ≠ ⊤ := (isCompact_univ.measure_lt_top).ne
  rw [h, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hu
  have hc : (Measure.haarScalarFactor ν (muK ε) : ℝ≥0∞) = 1 := by
    have := (ENNReal.mul_eq_right hpos htop).mp hu
    exact this
  rw [h, ENNReal.coe_eq_one.mp hc, one_smul]
end ReciprocityTheory.ChartRestriction.DS.S7
