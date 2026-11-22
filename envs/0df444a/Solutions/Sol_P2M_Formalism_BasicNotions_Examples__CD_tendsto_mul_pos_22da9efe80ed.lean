-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_tendsto_mul_pos_22da9efe80ed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:08.14741+00:00
-- url     : https://prove2.me/submissions/d74bbd85-812d-43fc-b9b9-a009657e42c6

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LeOfEventuallyDown

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Metric Filter Topology Module
open scoped ENNReal NNReal
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution {t : ℝ} (ht : 0 < t) :
    Tendsto (fun r : ℝ => t * r) (𝓝[>] 0) (𝓝[>] 0) := by
  have hc : Tendsto (fun r : ℝ => t * r) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun r : ℝ => t * r) (𝓝 0) (𝓝 (t * 0)) := tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_nhdsWithin_iff.mpr ⟨hc, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact mul_pos ht hr
end Formalism.BasicNotions.Examples₂.CD
