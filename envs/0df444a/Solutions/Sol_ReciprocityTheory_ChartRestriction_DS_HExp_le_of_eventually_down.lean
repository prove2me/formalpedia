-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.le_of_eventually_down
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:10:28.522503+00:00
-- url     : https://prove2.me/submissions/e69ffab9-0ee8-409e-b99e-e9cd7e5af3bd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_tendsto_mul_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HExp
open MeasureTheory Metric Filter Topology Module
open scoped ENNReal NNReal
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable (lam nu : Measure V) [lam.IsAddHaarMeasure] [IsFiniteMeasure nu]
namespace ReciprocityTheory.ChartRestriction.DS.HExp
theorem _root_.solution {ε δ : ℝ} (hε0 : 0 < ε) (hq : QInv nu ε δ) (M M' : ℝ≥0)
    (hM : (M' : ℝ≥0∞) * ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) ≤ M)
    (hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), M * lam (closedBall 0 r) ≤ nu (closedBall 0 r))
    (s : Set V) (hs : s ⊆ ball 0 δ) : M' * lam s ≤ nu s := by
  have key := (Besicovitch.vitaliFamily lam).measure_le_of_frequently_le (ρ := M' • lam) nu
    (Measure.AbsolutelyContinuous.smul_left (Measure.AbsolutelyContinuous.refl lam) M') s ?_
  · rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at key
    exact key
  intro X hX
  have hXn : ‖X‖ < δ := by simpa using hs hX
  have ht : Tendsto (fun r : ℝ => closedBall X ((1 + ε) * r)) (𝓝[>] 0)
      ((Besicovitch.vitaliFamily lam).filterAt X) :=
    (Besicovitch.tendsto_filterAt lam X).comp (tendsto_mul_pos (by linarith))
  refine ht.frequently (Eventually.frequently ?_)
  have hδ : 0 < δ := lt_of_le_of_lt (norm_nonneg _) hXn
  filter_upwards [hev, Ioo_mem_nhdsGT hδ] with r hr hrδ
  calc (M' • lam) (closedBall X ((1 + ε) * r))
      = (M' * ENNReal.ofReal ((1 + ε) ^ finrank ℝ V)) * lam (closedBall 0 r) := by
        rw [Measure.smul_apply, Measure.addHaar_closedBall_mul_of_pos lam X (by linarith) r,
          ENNReal.smul_def, smul_eq_mul, mul_assoc]
    _ ≤ M * lam (closedBall 0 r) := by gcongr
    _ ≤ nu (closedBall 0 r) := hr
    _ ≤ nu (closedBall X ((1 + ε) * r)) := (hq X hXn r hrδ.1 hrδ.2).2
end ReciprocityTheory.ChartRestriction.DS.HExp
