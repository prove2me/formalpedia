-- Prove2me | solution 1 for PositivityTheory.PfBern.Frob.FrMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:32:09.641977+00:00
-- url     : https://prove2.me/submissions/f9afa8c6-9d23-437c-8e4b-474681b3ab36

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TrivSymmApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousSectionQuotientStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_HaarDistr
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSchwartzBruhatCharacterIntegralOneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHaarRightInvariantStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_FrobProof
import Theorems.Thm_PositivityTheory_PfBern_Frob_span_fap
import Theorems.Thm_PositivityTheory_PfBern_Frob_FrMap_apply

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
theorem _root_.solution (uG : IsUnimod G) (uH : IsUnimod H)
    (hχ : Continuous fun g => (χ g : ℂ)) (α0 : SB G)
    (hα0 : ∫ g, (α0 : G → ℂ) g * (χ g : ℂ) ∂μG = 1) :
    Function.Injective (FrMap hp σ hpc μH μG χ uG uH hχ α0 hα0) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ξ hξ
  have h0 : ∀ φ, (ξ : Distr X) (fap hp σ hpc μH α0 φ) = 0 := fun φ => by
    have := LinearMap.congr_fun (congrArg Subtype.val hξ) φ
    rw [FrMap_apply] at this
    exact this
  apply Subtype.ext
  show (ξ : Distr X) = 0
  apply LinearMap.ext_on_range (span_fap hp σ hpc μH)
  rintro ⟨α, φ⟩
  show (ξ : Distr X) (fap hp σ hpc μH α φ) = 0
  rw [eval_fap hp σ hpc μH μG χ hχ ξ α0 hα0, h0, mul_zero]
end PositivityTheory.PfBern.Frob
