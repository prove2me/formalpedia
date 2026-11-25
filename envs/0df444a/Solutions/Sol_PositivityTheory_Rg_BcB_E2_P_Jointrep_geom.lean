-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.Jointrep.geom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:32:52.559853+00:00
-- url     : https://prove2.me/submissions/adb93860-4d68-4048-9f53-56100492fa52

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Jointrep

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
open PositivityTheory.Rg.BcB.E2.P.Jointrep
namespace PositivityTheory.Rg.BcB.E2.P.Jointrep
theorem _root_.solution : (∑' j : ℕ, ((2 : ℝ≥0∞)⁻¹ ^ j) ^ 2) ≠ ⊤ := by
  have h2 : (∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ j) ≠ ⊤ := by
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  refine ne_top_of_le_ne_top h2 (ENNReal.tsum_le_tsum fun j => ?_)
  exact pow_le_of_le_one (by simp) (pow_le_one₀ (by simp) (ENNReal.inv_le_one.2 one_le_two)) two_ne_zero
end PositivityTheory.Rg.BcB.E2.P.Jointrep
