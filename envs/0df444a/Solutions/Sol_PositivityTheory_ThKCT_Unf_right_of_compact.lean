-- Prove2me | solution 1 for PositivityTheory.ThKCT.Unf.right_of_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:00:14.360886+00:00
-- url     : https://prove2.me/submissions/bfc9ee30-6543-467d-aaa1-b00f29870b9d

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_RightOfCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal NNReal Pointwise
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Unf
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace PositivityTheory.ThKCT.Unf
theorem _root_.solution [CompactSpace G] (μ : Measure G) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have e := Measure.isMulLeftInvariant_eq_smul (μ.map (· * g)) μ
  have h := congrArg (fun m : Measure G => m univ) e
  simp only [Measure.smul_apply] at h
  rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, preimage_univ, ENNReal.smul_def, smul_eq_mul] at h
  have h1 : (Measure.haarScalarFactor (μ.map (· * g)) μ : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj (isOpen_univ.measure_ne_zero μ univ_nonempty) (measure_ne_top μ _)).1 (by rw [← h, one_mul])
  rw [e, ENNReal.coe_eq_one.1 h1, one_smul]
end PositivityTheory.ThKCT.Unf
