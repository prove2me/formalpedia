-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Two.Dat.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:56.971087+00:00
-- url     : https://prove2.me/submissions/a6050d8f-8bab-4726-a9ec-1489fa0976d5

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont
import Theorems.Thm_PositivityTheory_ThKEnd_Two_Bump_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Two
open MeasureTheory Topology Filter
open scoped Pointwise
variable {G X : Type} [Group G] [TopologicalSpace G]
variable [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {Γ : Subgroup G} {n : X → G} {a : G} {lam : Measure X}
  [IsProbabilityMeasure lam] {l : ℂ} {φ c : G → ℂ} {V : Set G} {η : G → ℝ} (μ : Measure G) [μ.IsHaarMeasure]
omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [TopologicalSpace X] [OpensMeasurableSpace X] [IsProbabilityMeasure lam]
namespace PositivityTheory.ThKEnd.Two
namespace Dat
theorem _root_.solution (h : Dat Γ n a lam l φ c) (k : ℕ) (g : G) : c (a * (a ^ k * g)) - c (a ^ k * g) = l ^ k * (c (a * g) - c g) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ' a, mul_assoc, h.law, ih, pow_succ' l, mul_assoc]
end Dat
end PositivityTheory.ThKEnd.Two
