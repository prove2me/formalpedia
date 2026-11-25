-- Prove2me | solution 1 for PositivityTheory.PfBern.Frob.supportedIn_FrMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:23:19.876465+00:00
-- url     : https://prove2.me/submissions/04da0a40-abe1-4b6e-beb8-761ab002aec2

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TrivSymmApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousSectionQuotientStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_HaarDistr
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSchwartzBruhatCharacterIntegralOneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHaarRightInvariantStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_FrobProof
import Theorems.Thm_PositivityTheory_PfBern_Frob_avg_lift
import Theorems.Thm_PositivityTheory_PfBern_Frob_exists_schwartz_integral_one
import Theorems.Thm_PositivityTheory_PfBern_Frob_FrMap_apply
import Theorems.Thm_PositivityTheory_PfBern_Frob_fap_apply
import Theorems.Thm_PositivityTheory_PfBern_Frob_intB_apply
import Theorems.Thm_PositivityTheory_PfBern_Frob_rtr_apply
import Theorems.Thm_PositivityTheory_PfBern_Frob_tens_induction
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
theorem _root_.solution (uG : IsUnimod G) (uH : IsUnimod H)
    (hχ : Continuous fun g => (χ g : ℂ)) (α0 : SB G)
    (hα0 : ∫ g, (α0 : G → ℂ) g * (χ g : ℂ) ∂μG = 1) (ξ : eqv X χ) (C : Set X)
    (hC : ∀ (g : G), ∀ x ∈ C, g • x ∈ C) :
    SupportedIn (ξ : Distr X) C ↔
      SupportedIn ((FrMap hp σ hpc μH μG χ uG uH hχ α0 hα0 ξ : eqvF hp _) : Distr (Fib p))
        (Subtype.val ⁻¹' C) := by
  constructor
  · intro hξ φ hφ
    rw [FrMap_apply]
    apply hξ
    intro x hx
    by_contra hxC
    rw [Set.mem_compl_iff, not_not] at hxC
    apply hx
    rw [fap_apply]
    have h0 : ∀ h : H, (φ : Fib p → ℂ) (fibSmul hp h⁻¹ (zpart hp σ x)) = 0 := by
      intro h
      by_contra hne
      have hc := hφ hne
      apply hc
      show ((h⁻¹ : H) : G) • ((σ.s (p x))⁻¹ • x) ∈ C
      exact hC _ _ (hC _ _ hxC)
    simp [h0]
  · intro hF f hf
    obtain ⟨b0, hb0⟩ := exists_schwartz_integral_one μH
    rw [← avg_lift hp σ hpc μH b0 hb0 f]
    have key3 : ((ξ : Distr X) ∘ₗ avg hp σ hpc μH)
        (pullHomeo (triv hp σ hpc).symm (tens f b0)) ∈ (⊥ : Submodule ℂ ℂ) := by
      refine tens_induction _ ⊥ _ (fun a b hab => ?_)
      rw [Submodule.mem_bot]
      show (ξ : Distr X) (fap hp σ hpc μH a b) = 0
      rw [eval_fap hp σ hpc μH μG χ hχ ξ α0 hα0]
      by_cases ha : ∃ g, (a : G → ℂ) g ≠ 0
      · obtain ⟨g, hg⟩ := ha
        have hb : (ξ : Distr X) (fap hp σ hpc μH α0 b) = 0 := by
          rw [← FrMap_apply hp σ hpc μH μG χ uG uH hχ α0 hα0]
          apply hF
          intro z hz hzC
          have h1 := hab (g, z) hg hz
          simp only [pullHomeo_apply, triv_symm_apply, tens_apply] at h1
          exact hf (left_ne_zero_of_mul h1) (hC g _ hzC)
        rw [hb, mul_zero]
      · push_neg at ha
        have : ∫ g, (a : G → ℂ) g * (χ g : ℂ) ∂μG = 0 := by simp [ha]
        rw [this, zero_mul]
    rw [Submodule.mem_bot] at key3
    exact key3
end PositivityTheory.PfBern.Frob
