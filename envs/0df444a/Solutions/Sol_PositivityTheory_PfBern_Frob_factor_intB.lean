-- Prove2me | solution 1 for PositivityTheory.PfBern.Frob.factor_intB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:02:27.095687+00:00
-- url     : https://prove2.me/submissions/2a1e1c49-f293-4e33-af55-4fd0f73b1c8a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultipleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzBruhatProdSpanTensorsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PartialIntegralMemSchwartzBruhatStatement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TensInduction
import Theorems.Thm_PositivityTheory_PfBern_Frob_tens_induction
import Theorems.Thm_PositivityTheory_PfBern_Frob_intB_apply
import Theorems.Thm_PositivityTheory_PfBern_Frob_intB_tens
import Theorems.Thm_PositivityTheory_PfBern_Frob_rtr_apply
import Theorems.Thm_GlobalTheory_T_invariant_functional_eq_haar_multiple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.PfBern.Frob.intB_apply
attribute [local simp] PositivityTheory.PfBern.Frob.rtr_apply

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
theorem _root_.solution (uK : IsUnimod K) (b0 : SB K) (hb0 : ∫ y, (b0 : K → ℂ) y ∂μ = 1)
    (M : SB (A × K) →ₗ[ℂ] ℂ) (hM : ∀ (k : K) (F : SB (A × K)), M (rtr k F) = M F)
    (F : SB (A × K)) :
    M F = M (tens (intB μ (fun _ => (1 : ℂ)) continuous_const F) b0) := by
  have hc : ∀ a : SB A, ∃ c : ℂ, ∀ b : SB K, M (tens a b) = c * ∫ y, (b : K → ℂ) y ∂μ := by
    intro a
    refine GlobalTheory.T.invariant_functional_eq_haar_multiple K uK μ (M ∘ₗ tensR a) ?_
    intro k b
    have e : tens a (pullHomeo (Homeomorph.mulRight k) b) = rtr k (tens a b) := rfl
    show M (tens a (pullHomeo (Homeomorph.mulRight k) b)) = M (tens a b)
    rw [e, hM]
  choose c hc using hc
  let T : SB (A × K) →ₗ[ℂ] ℂ :=
    M - M ∘ₗ tensL b0 ∘ₗ intB μ (fun _ => (1 : ℂ)) continuous_const
  have key : T F ∈ (⊥ : Submodule ℂ ℂ) := by
    refine tens_induction T ⊥ F (fun a b _ => ?_)
    rw [Submodule.mem_bot]
    show M (tens a b) - M (tensL b0 (intB μ (fun _ => (1 : ℂ)) continuous_const (tens a b))) = 0
    rw [intB_tens, LinearMap.map_smul, tensL_apply, LinearMap.map_smul, hc, hc, hb0]
    simp only [mul_one, smul_eq_mul]
    ring
  rw [Submodule.mem_bot] at key
  exact sub_eq_zero.1 key
end PositivityTheory.PfBern.Frob
