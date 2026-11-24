-- Prove2me | solution 1 for PositivityTheory.PfBern.Frob.intB_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:56:39.645967+00:00
-- url     : https://prove2.me/submissions/2851552d-3c8d-48d7-a72e-d96004b24be1

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultipleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzBruhatProdSpanTensorsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PartialIntegralMemSchwartzBruhatStatement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TensInduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Set MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Frob
variable {A B : Type} [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A]
  [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B]
  [TotallyDisconnectedSpace B] [MeasurableSpace B] [BorelSpace B]
  (μ : Measure B) [IsFiniteMeasureOnCompacts μ]
namespace PositivityTheory.PfBern.Frob
theorem _root_.solution (w : B → ℂ) (hw : Continuous w) (F : SB (A × B)) (a : A) :
    ((intB μ w hw F : SB A) : A → ℂ) a = ∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ :=
  rfl
end PositivityTheory.PfBern.Frob
