-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RatPosPartLocal_proof_6e65cebccefc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:10:02.775807+00:00
-- url     : https://prove2.me/submissions/e55ab1d0-5d2a-46c7-ae1f-005acff3f6bb

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatPosPartLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatPosPartLocal_isOpen_ne_zero_8867941ae2ad
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatPosPartLocal_continuousOn_ratMap_76c7d0659315
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatPosPartLocal_ratPosDens_eq_86bec30a717e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticOnNhd_of_differentiableOn_d56f1b066651
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_maDens_congr_of_eventuallyEq_290b4083a720
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PosPartLocal_chartPosDens_eq_4dc56fd33f6f
import Theorems.Thm_ReciprocityTheory_AnForm_A_lintegral_image_eq_lintegral_normSq_det_mul
import Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace RatPosPartLocal
theorem _root_.solution : RatPosPartLocal.Statement := by
  rintro n d J A p q f φ x - hφ ⟨s, U, hU, hxU, hsd, -, hsec, V, hV, hVs⟩
    ⟨s', U', hU', hxU', hsd', hsx', hsec', V', hV', hVs'⟩
  have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
  set Q := {z : Fin n → ℂ | eval z q ≠ 0} with hQdef
  have hD' : IsOpen (Q ∩ RatChart.ratMap p q ⁻¹' U') :=
    (RatPosPartLocal.continuousOn_ratMap p q).isOpen_inter_preimage (RatPosPartLocal.isOpen_ne_zero q) hU'
  set W := (interior V ∩ (fun z => A *ᵥ z) ⁻¹' U) ∩ (interior V' ∩ (Q ∩ RatChart.ratMap p q ⁻¹' U'))
    with hWdef
  have hW : IsOpen W :=
    (isOpen_interior.inter (hU.preimage hAc)).inter (isOpen_interior.inter hD')
  have hWs : ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ s (A *ᵥ x') = x' :=
    by rintro x' ⟨hZ, ⟨hV1, hU1⟩, -⟩; exact ⟨hU1, (hVs x' ⟨hZ, interior_subset hV1⟩ hU1).symm⟩
  have hWs' : ∀ x' ∈ zeroSet J ∩ W,
      eval x' q ≠ 0 ∧ RatChart.ratMap p q x' ∈ U' ∧ s' (RatChart.ratMap p q x') = x' :=
    by
      rintro x' ⟨hZ, -, ⟨hV1, hq1, hU1⟩⟩
      exact ⟨hq1, hU1, (hVs' x' ⟨hZ, interior_subset hV1⟩ hq1 hU1).symm⟩
  have hxq : eval x q ≠ 0 := by
    have h := (hsec' _ hxU').2.1
    rwa [hsx'] at h
  refine ⟨W, hW, ⟨⟨mem_interior_iff_mem_nhds.2 hV, hxU⟩, ⟨mem_interior_iff_mem_nhds.2 hV', hxq, hxU'⟩⟩,
    fun E _ hEW => ?_⟩
  simp_rw [PosPartLocal.chartPosDens_eq hU hsd hsec hW hWs hEW,
    RatPosPartLocal.ratPosDens_eq hU' hsd' hsec' hW hWs' hEW]

  set O' := U' ∩ s' ⁻¹' W with hO'def
  set τ : (Fin d → ℂ) → Fin d → ℂ := fun z => A *ᵥ s' z with hτdef
  have hO' : IsOpen O' := hsd'.continuousOn.isOpen_inter_preimage hU' hW
  have hτU : ∀ z ∈ O', τ z ∈ U ∧ s (τ z) = s' z := fun z hz => hWs _ ⟨(hsec' z hz.1).1, hz.2⟩
  have hτd : DifferentiableOn ℂ τ O' := by
    have hs'O : DifferentiableOn ℂ s' O' := hsd'.mono Set.inter_subset_left
    exact ((Matrix.mulVecLin A).toContinuousLinearMap.differentiable.comp_differentiableOn hs'O)
  have hτan : AnalyticOnNhd ℂ τ O' := IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hO' hτd
  have hτinj : Set.InjOn τ O' := fun z₁ h₁ z₂ h₂ h => by
    have h' := congrArg s h
    rw [(hτU z₁ h₁).2, (hτU z₂ h₂).2] at h'
    rw [← (hsec' z₁ h₁.1).2.2, ← (hsec' z₂ h₂.1).2.2, h']
  have hsan : AnalyticOnNhd ℂ s U := IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hU hsd
  calc _ = ∫⁻ y in τ '' O', ENNReal.ofReal ((U ∩ s ⁻¹' E).indicator
          (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) y) := by
        refine (setLIntegral_eq_of_support_subset fun y hy => ?_).symm
        have hyE : y ∈ U ∩ s ⁻¹' E := by
          by_contra h
          exact hy (by simp [Set.indicator_of_notMem h])
        have hZ : s y ∈ zeroSet J ∩ W := ⟨(hsec y hyE.1).2, hEW hyE.2⟩
        refine ⟨RatChart.ratMap p q (s y), ⟨(hWs' _ hZ).2.1, ?_⟩, ?_⟩
        · show s' (RatChart.ratMap p q (s y)) ∈ W
          rw [(hWs' _ hZ).2.2]
          exact hZ.2
        · show A *ᵥ s' (RatChart.ratMap p q (s y)) = y
          rw [(hWs' _ hZ).2.2, (hsec y hyE.1).1]
    _ = ∫⁻ z in O', ENNReal.ofReal (Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det) *
          ENNReal.ofReal ((U ∩ s ⁻¹' E).indicator
            (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) (τ z)) :=
        ReciprocityTheory.AnForm.A.lintegral_image_eq_lintegral_normSq_det_mul τ O' hO' hτan hτinj _
    _ = ∫⁻ z in O', ENNReal.ofReal ((U' ∩ s' ⁻¹' E).indicator
          (fun y => max (f (s' y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s') y) 0) z) := by
        refine setLIntegral_congr_fun hO'.measurableSet fun z hz => ?_
        by_cases hzE : s' z ∈ E
        · have hm : τ z ∈ U ∩ s ⁻¹' E :=
            ⟨(hτU z hz).1, by rw [Set.mem_preimage, (hτU z hz).2]; exact hzE⟩
          rw [Set.indicator_of_mem hm, Set.indicator_of_mem (show z ∈ U' ∩ s' ⁻¹' E from ⟨hz.1, hzE⟩)]
          have h1 : ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s') z =
              ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ τ) z :=
            IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k => by
              filter_upwards [hO'.mem_nhds hz] with w hw
              show φ k (s' w) = φ k (s (τ w))
              rw [(hτU w hw).2]
          have h2 : ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ τ) z =
              ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (τ z) *
                Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det := by
            refine ReciprocityTheory.AnForm.A.maDens_comp (fun k => φ k ∘ s) τ z (hτan z hz) fun k => ?_
            obtain ⟨Ok, hOk, hZOk, hφk⟩ := hφ k
            have hsZ : s (τ z) ∈ Ok := hZOk (by rw [(hτU z hz).2]; exact (hsec' z hz.1).1)
            have hφa : ContDiffAt ℝ 2 (φ k) (s (τ z)) :=
              (hφk.contDiffAt (hOk.mem_nhds hsZ)).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
            have hsa : ContDiffAt ℝ 2 s (τ z) :=
              ((hsan (τ z) (hτU z hz).1).contDiffAt).restrict_scalars ℝ
            exact hφa.comp (τ z) hsa
          rw [h1, h2, (hτU z hz).2, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _), mul_comm,
            max_mul_of_nonneg _ _ (Complex.normSq_nonneg _), zero_mul, mul_assoc]
        · rw [Set.indicator_of_notMem (fun hm => hzE (by
              have := hm.2
              rw [Set.mem_preimage, (hτU z hz).2] at this
              exact this)),
            Set.indicator_of_notMem (show z ∉ U' ∩ s' ⁻¹' E from fun hm => hzE hm.2)]
          simp
    _ = _ := by
        refine setLIntegral_eq_of_support_subset fun z hz => ?_
        have hzE : z ∈ U' ∩ s' ⁻¹' E := by
          by_contra h
          exact hz (by simp [Set.indicator_of_notMem h])
        exact ⟨hzE.1, hEW hzE.2⟩
end RatPosPartLocal
end GroundTheory.Heights₂.Heights
