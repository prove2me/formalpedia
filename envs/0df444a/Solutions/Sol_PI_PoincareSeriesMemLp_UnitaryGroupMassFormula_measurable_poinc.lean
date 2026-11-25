-- Prove2me | solution 1 for PI.PoincareSeriesMemLp.UnitaryGroupMassFormula.measurable_poinc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:03:43.492123+00:00
-- url     : https://prove2.me/submissions/ca40907c-04b0-4a0a-9565-ca3ff3e49514

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_FoldBound
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_PoincareSeriesSquareIntegrable
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FoldUnfold
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FoldMult
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PoincareSeriesMeasurability_FoldL2DoubleCoset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open PI PI.PoincareSeriesMemLp PI.PoincareSeriesMemLp.UnitaryGroupMassFormula
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable
namespace PI.PoincareSeriesMemLp.UnitaryGroupMassFormula
theorem _root_.solution {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (D : Set G) [Countable D] (Ph : G → ℂ) (hPh : Measurable Ph)
    (hs : ∀ x, (∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ) ≠ ⊤) : Measurable (poinc D Ph) := by
  have hsum : ∀ x, Summable (fun δ : D => Ph ((δ : G) * x)) := by
    intro x
    have h1 : Summable (fun δ : D => ‖Ph ((δ : G) * x)‖₊) := by
      have h2 := hs x
      simp only [enorm_eq_nnnorm] at h2
      exact ENNReal.tsum_coe_ne_top_iff_summable.mp h2
    exact Summable.of_norm (by simpa using NNReal.summable_coe.mpr h1)
  refine measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset D))
    (f := fun (s : Finset D) x => ∑ δ ∈ s, Ph ((δ : G) * x)) (fun s => ?_) ?_
  · exact Finset.measurable_sum _ (fun δ _ => hPh.comp (measurable_const_mul _))
  · rw [tendsto_pi_nhds]
    intro x
    unfold poinc
    exact (hsum x).hasSum
end PI.PoincareSeriesMemLp.UnitaryGroupMassFormula
