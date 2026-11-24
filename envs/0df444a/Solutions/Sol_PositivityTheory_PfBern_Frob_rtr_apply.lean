-- Prove2me | solution 1 for PositivityTheory.PfBern.Frob.rtr_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:56:59.331101+00:00
-- url     : https://prove2.me/submissions/001ba8db-2eca-4cd9-9ac2-5cacd50df35b

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
variable {A : Type} [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A]
  [TotallyDisconnectedSpace A]
  {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K]
  [LocallyCompactSpace K] [TotallyDisconnectedSpace K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [μ.IsHaarMeasure]
namespace PositivityTheory.PfBern.Frob
theorem _root_.solution (k : K) (F : SB (A × K)) (q : A × K) :
    ((rtr k F : SB (A × K)) : A × K → ℂ) q = (F : A × K → ℂ) (q.1, q.2 * k) :=
  rfl
end PositivityTheory.PfBern.Frob
