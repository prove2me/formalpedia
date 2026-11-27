-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ParamPieceInt_proof_92d128599d04
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:06:49.594478+00:00
-- url     : https://prove2.me/submissions/16ae1dd2-3ad7-45e1-a995-124b915bd77d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParamPieceInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PParamPieceInt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ParamPieceInt_analyticAt_of_differentiableOn_516a147c42f5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ParamPieceInt_differentiable_mulVec_67d96b3ba5df
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ParamPieceInt_exists_sheet_964cabc34eb6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_maDens_congr_of_eventuallyEq_290b4083a720
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_sheet_eventuallyEq_f5b44630f2f2
import Theorems.Thm_ReciprocityTheory_AnForm_A_det_fderiv_real_eq_normSq
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
open scoped ContDiff
noncomputable section
open ParamPieceInt
namespace GroundTheory.Heights₂.Heights
namespace ParamPieceInt
theorem _root_.solution : ParamPieceInt.Statement := by
  intro n d W A σ r r' N hσ hinj hN hrr hprop hcov f φ P hφ hPm hPb hPw hgP
  classical
  set g : (Fin d → ℂ) → Fin d → ℂ := fun v => A *ᵥ σ v with hg
  have hgd : DifferentiableOn ℂ g (Metric.ball 0 r) :=
    (differentiable_mulVec A).comp_differentiableOn hσ
  have hgan : ∀ v ∈ Metric.ball (0 : Fin d → ℂ) r, AnalyticAt ℂ g v := fun v hv =>
    analyticAt_of_differentiableOn Metric.isOpen_ball hgd hv

  have hdens : ∀ w ∈ P, Complex.normSq (ReciprocityTheory.AnForm.A.jacC g w).det *
      chartDens W A ((σ '' P).indicator f) φ (g w) =
        f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w := by
    intro w hw
    obtain ⟨s, hs, hsg⟩ := exists_sheet hσ hinj hN hrr hprop hcov (hPb hw) (hPw w hw).1 (hPw w hw).2
    have hex : ∃ s, IsSheetAt W A (σ w) s := ⟨s, hs⟩
    have hfib : σ w ∈ fibre W A (g w) := ⟨(hprop w (hPb hw) (hPw w hw).1).1, rfl⟩
    have hsum : chartDens W A ((σ '' P).indicator f) φ (g w) =
        f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (g w) := by
      unfold chartDens sheetSum
      rw [finsum_eq_single _ (σ w), finsum_eq_if, if_pos hfib, dif_pos hex]
      · beta_reduce
        rw [Set.indicator_of_mem (Set.mem_image_of_mem σ hw), IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k =>
          (SheetSumMeasurable.sheet_eventuallyEq hs hex.choose_spec).fun_comp (φ k)]
      · intro x hxne
        rw [finsum_eq_if]
        split_ifs with hx h
        · beta_reduce
          rw [Set.indicator_of_notMem, zero_mul]
          rintro ⟨w', hw', rfl⟩
          exact hxne (by rw [hgP hw' hw hx.2])
        · rfl
        · rfl

    obtain ⟨U, hUo, hwU, hsd, hsx, -, -⟩ := hs
    have hsc : ContDiffAt ℝ 2 s (g w) :=
      (analyticAt_of_differentiableOn hUo hsd hwU).contDiffAt.restrict_scalars ℝ
    have hφs : ∀ k, ContDiffAt ℝ 2 (φ k ∘ s) (g w) := by
      intro k
      obtain ⟨Uk, hUko, hZU, hcd⟩ := hφ k
      have hmem : s (g w) ∈ Uk := by
        show s (A *ᵥ σ w) ∈ Uk
        rw [hsx]; exact hZU (hprop w (hPb hw) (hPw w hw).1).1
      exact ((hcd.contDiffAt (hUko.mem_nhds hmem)).of_le
        (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))).comp (g w) hsc
    have hcomp : ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ g) w =
        ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (g w) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC g w).det :=
      ReciprocityTheory.AnForm.A.maDens_comp (fun k => φ k ∘ s) g w (hgan w (hPb hw)) hφs
    have hev : ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w =
        ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ g) w :=
      IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k => by
        filter_upwards [hsg] with v hv
        simp only [Function.comp_apply, g]
        rw [hv]
    rw [hsum, hev, hcomp]
    ring

  have hzero : ∀ y, y ∉ g '' P → chartDens W A ((σ '' P).indicator f) φ y = 0 := by
    intro y hy
    unfold chartDens sheetSum
    refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx => ?_
    split_ifs with h
    · beta_reduce
      rw [Set.indicator_of_notMem, zero_mul]
      rintro ⟨w, hw, rfl⟩
      exact hy ⟨w, hw, hx.2⟩
    · rfl
  have hgdP : ∀ w ∈ P, DifferentiableAt ℂ g w := fun w hw => (hgan w (hPb hw)).differentiableAt
  unfold chartInt
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    integral_image_eq_integral_abs_det_fderiv_smul volume hPm
      (fun x hx => ((hgdP x hx).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt) hgP]
  refine setIntegral_congr_fun hPm fun w hw => ?_
  rw [ReciprocityTheory.AnForm.A.det_fderiv_real_eq_normSq g w (hgdP w hw),
    abs_of_nonneg (Complex.normSq_nonneg _), smul_eq_mul, hdens w hw]
end ParamPieceInt
end GroundTheory.Heights₂.Heights
