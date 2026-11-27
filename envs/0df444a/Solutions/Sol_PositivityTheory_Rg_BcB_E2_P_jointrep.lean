-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.jointrep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:21:33.955452+00:00
-- url     : https://prove2.me/submissions/24f02a8b-047e-451d-8db4-43e24fe501eb

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Jointrep
import Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Jointrep_ae_tendsto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P
open Jointrep
namespace PositivityTheory.Rg.BcB.E2.P
theorem _root_.solution : JointRep := by
  classical
  intro S _ ν _ _ _
  set u := TopologicalSpace.denseSeq (Lp ℂ 2 ν) with hu
  have hex : ∀ (j : ℕ) (h : Lp ℂ 2 ν), ∃ n, edist h (u n) < (2⁻¹ : ℝ≥0∞) ^ j := by
    intro j h
    obtain ⟨y, ⟨n, rfl⟩, hy⟩ := EMetric.mem_closure_iff.1
      (TopologicalSpace.denseRange_denseSeq (Lp ℂ 2 ν) h) _
      (ENNReal.pow_pos (ENNReal.inv_pos.2 (by simp : (2 : ℝ≥0∞) ≠ ⊤)) j)
    exact ⟨n, hy⟩
  let N : ℕ → Lp ℂ 2 ν → ℕ := fun j h => Nat.find (hex j h)
  have hN : ∀ j, Measurable (N j) := fun j =>
    measurable_find (hex j) fun n => Metric.isOpen_eball.measurableSet
  refine ⟨fun h s => limUnder atTop (fun j => (u (N j h) : S → ℂ) s), ?_, fun h => ?_⟩
  · have hf : ∀ j, StronglyMeasurable (fun p : Lp ℂ 2 ν × S => (u (N j p.1) : S → ℂ) p.2) := by
      intro j
      have m : Measurable (fun q : S × ℕ => (u q.2 : S → ℂ) q.1) :=
        measurable_from_prod_countable_left fun n => (Lp.stronglyMeasurable (u n)).measurable
      exact (m.comp (measurable_snd.prodMk ((hN j).comp measurable_fst))).stronglyMeasurable
    exact (StronglyMeasurable.limUnder (l := atTop) hf).measurable
  · filter_upwards [ae_tendsto h (fun j => u (N j h)) fun j => Nat.find_spec (hex j h)] with s hs
    exact hs.limUnder_eq
end PositivityTheory.Rg.BcB.E2.P
