-- Prove2me | solution 1 for P2M_Auto_aux_integrable_wienerEnvelope_of_integrable__1e1fced5a7d3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:45:16.512805+00:00
-- url     : https://prove2.me/submissions/f0e4c639-8fea-4114-9c1a-0a15d3648342

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_continuous_wienerEnvelope
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_aux_exists_finite_closedBall_cover
public import Theorems.Thm_Auto_aux_wienerEnvelope_le_sum_of_cover

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E]
    [ProperSpace E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddRightInvariant (volume : Measure E)] [NormedAddCommGroup F]
    {f : E → F} (hf : Continuous f) {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s)
    (hfr : Integrable (wienerEnvelope f r)) :
    Integrable (wienerEnvelope f s) := by
  classical
  obtain ⟨t, ht⟩ := aux_exists_finite_closedBall_cover (E := E) r hr s
  have hsum : Integrable (fun x ↦ ∑ z ∈ t, wienerEnvelope f r (x + z)) := by
    apply integrable_finsetSum
    intro z hz
    exact hfr.comp_add_right z
  refine hsum.mono_nonneg (continuous_wienerEnvelope hf s).aestronglyMeasurable
    (ae_of_all _ fun x ↦ aux_wienerEnvelope_nonneg hf hs x) (ae_of_all _ fun x ↦ ?_)
  exact aux_wienerEnvelope_le_sum_of_cover hf (le_of_lt hr) hs t ht x
end Auto
