-- Prove2me | solution 1 for PositivityTheory.PfBern.Frob.exists_schwartz_integral_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:54:39.034995+00:00
-- url     : https://prove2.me/submissions/8c0b7fac-7336-4c32-9839-c4f48b33908e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TrivSymmApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousSectionQuotientStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_HaarDistr
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSchwartzBruhatCharacterIntegralOneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHaarRightInvariantStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_FrobProof
import Theorems.Thm_GlobalTheory_T_exists_schwartzBruhat_character_integral_one
import Theorems.Thm_PositivityTheory_PfBern_Frob_intB_apply
import Theorems.Thm_PositivityTheory_PfBern_Frob_rtr_apply
import Theorems.Thm_PositivityTheory_PfBern_Frob_triv_apply
import Theorems.Thm_PositivityTheory_PfBern_Frob_triv_symm_apply
import Theorems.Thm_PositivityTheory_RgUd_T2_HaarDistr_mulLC_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.PfBern.Frob.intB_apply
attribute [local simp] PositivityTheory.PfBern.Frob.rtr_apply
attribute [local simp] PositivityTheory.PfBern.Frob.triv_apply
attribute [local simp] PositivityTheory.PfBern.Frob.triv_symm_apply
attribute [local simp] PositivityTheory.RgUd.T2.HaarDistr.mulLC_apply



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
theorem _root_.solution : ∃ b0 : SB H, ∫ y, (b0 : H → ℂ) y ∂μH = 1 := by
  obtain ⟨b0, hb0⟩ := GlobalTheory.T.exists_schwartzBruhat_character_integral_one H μH 1
    (by simp only [MonoidHom.one_apply, Units.val_one]; exact continuous_const)
  exact ⟨b0, by simpa using hb0⟩
end PositivityTheory.PfBern.Frob
