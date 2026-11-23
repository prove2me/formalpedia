-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hint_mpTail
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:52.940254+00:00
-- url     : https://prove2.me/submissions/9b3c55c3-e09c-4cdc-81b1-1e823d9ceb66

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintIntOfBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hint_mpSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.T0
open MeasureTheory ReciprocityTheory.MultiplicativeHeights
private theorem isProbabilityMeasure_sphereProb' (n : ℕ) (hn : 0 < n) : IsProbabilityMeasure (sphereProb n) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  unfold sphereProb
  have hpos : 0 < Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) := Module.finrank_pos
  have h1 : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ 0 := by
    rw [Measure.toSphere_apply_univ]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hpos.ne') (Metric.measure_ball_pos _ _ one_pos).ne'
  have h2 : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ ⊤ := by
    rw [Measure.toSphere_apply_univ]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_ball_lt_top.ne
  exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite h1 h2
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MeasureTheory ReciprocityTheory.MultiplicativeHeights
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (D n : ℕ) (hn : 0 < n) :
    MeasurePreserving (fun z : BlockSphere (D + 1) n => fun i : Fin D => z i.succ)
      (blockSphereProb (D + 1) n) (blockSphereProb D n) := by
  haveI := isProbabilityMeasure_sphereProb' n hn
  haveI : SFinite (blockSphereProb D n) := by
    unfold blockSphereProb
    infer_instance
  have h := (measurePreserving_snd (μ := sphereProb n) (ν := blockSphereProb D n)).comp
    (hint_mpSplit D n hn)
  have e : (fun z : BlockSphere (D + 1) n => fun i : Fin D => z i.succ) =
      Prod.snd ∘ ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => UnitSphereC n) 0) := by
    funext z i
    first
      | rfl
      | (simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.removeNth]; done)
      | (simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.removeNth]; rfl)
      | exact congrArg z (by simp)
  rw [e]
  exact h
end ReciprocityTheory.ChartRestriction.G.T0
