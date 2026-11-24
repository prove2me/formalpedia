-- Prove2me | solution 1 for PositivityTheory.PfBern.Frob.intB_tens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:07:22.576489+00:00
-- url     : https://prove2.me/submissions/7dbab6ec-12d8-4c42-b35b-19d124782b53

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultipleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzBruhatProdSpanTensorsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PartialIntegralMemSchwartzBruhatStatement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TensInduction
import Theorems.Thm_PositivityTheory_PfBern_Frob_intB_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.PfBern.Frob.intB_apply

set_option autoImplicit false
noncomputable section
open Set MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Frob
variable {A B : Type} [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A]
  [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B]
  [TotallyDisconnectedSpace B] [MeasurableSpace B] [BorelSpace B]
  (μ : Measure B) [IsFiniteMeasureOnCompacts μ]
namespace PositivityTheory.PfBern.Frob
theorem _root_.solution (w : B → ℂ) (hw : Continuous w) (a : SB A) (b : SB B) :
    intB μ w hw (tens a b) = (∫ y, (b : B → ℂ) y * w y ∂μ) • a := by
  apply Subtype.ext
  funext x
  show ∫ y, ((a : A → ℂ) x * (b : B → ℂ) y) * w y ∂μ = (∫ y, (b : B → ℂ) y * w y ∂μ) * (a : A → ℂ) x
  simp only [mul_assoc]
  rw [integral_const_mul, mul_comm]
end PositivityTheory.PfBern.Frob
