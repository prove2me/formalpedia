-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.Specmeas.ofR_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:13.19561+00:00
-- url     : https://prove2.me/submissions/b5f334e7-ebe3-4fc4-ab3a-72c9a1a016b1

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Specmeas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ComplexConjugate ComplexOrder CompactlySupported
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P PositivityTheory.Rg.BcB.E2.P.Specmeas
variable {X : Type} [TopologicalSpace X]
namespace PositivityTheory.Rg.BcB.E2.P.Specmeas
theorem _root_.solution (g h : C(X, ℝ)) : ofR (g - h) = ofR g - ofR h := by
  ext x; simp
end PositivityTheory.Rg.BcB.E2.P.Specmeas
