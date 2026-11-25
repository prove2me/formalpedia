-- Prove2me | solution 1 for PositivityTheory.PfBern.Frob.intG_tens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:41:53.961221+00:00
-- url     : https://prove2.me/submissions/1cd985f7-1e6d-411a-9a96-ce222b8f9932

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TrivSymmApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousSectionQuotientStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_HaarDistr
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSchwartzBruhatCharacterIntegralOneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHaarRightInvariantStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_FrobProof

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
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {H : Subgroup G} [LocallyCompactSpace H]
  {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] [MulAction G X] [ContinuousSMul G X]
  {p : X → G ⧸ H} (hp : ∀ (g : G) (x : X), p (g • x) = g • p x) (σ : Sec H)
  (hpc : Continuous p) (μH : Measure H) [μH.IsHaarMeasure] [LocallyCompactSpace (Fib p)]
  (μG : Measure G) [μG.IsHaarMeasure] (χ : G →* ℂˣ)
namespace PositivityTheory.PfBern.Frob
theorem _root_.solution (hχ : Continuous fun g => (χ g : ℂ)) (α : SB G) (φ : SB (Fib p)) :
    intG μG χ hχ (tens α φ) = (∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG) • φ := by
  apply Subtype.ext
  funext z
  show ∫ g, ((α : G → ℂ) g * (φ : Fib p → ℂ) z) * (χ g : ℂ) ∂μG =
    (∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG) * (φ : Fib p → ℂ) z
  rw [← integral_mul_const]
  congr 1
  funext g
  ring
end PositivityTheory.PfBern.Frob
