-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_tendsto_varInt_fsLogReg_ea2fc2c53ba1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:03:10.23481+00:00
-- url     : https://prove2.me/submissions/fb05389a-85dc-428d-8a36-0d07453c5817

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceFormLelongCompactLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_chartAbsDens_indicator_eq_f674260ff31b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_integrable_chartDens_daacb8db24dc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_measurable_fsLogReg_f4332e7b3091
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_norm_chartDens_fsLogReg_le_7e372de618a5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_tendsto_chartDens_fsLogReg_533dead26d4b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMassCompact_proof_637e1cfa7406
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLogBound_proof_ab4a666aa1df
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffDominated_ae_eval_ne_zero_80133a975faf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffDominated_proof_e9b099c76968
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOff_proof_fa25535eea0a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongRegularise_ae_eval_ne_zero_9e323230ff5d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongRegularise_exists_poly_of_linEval_eq_zero_1a20ed7e007c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongRegularise_proof_dfe9c2a6cf8c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_ae_eval_ne_zero_e1e014cbbf7d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_proof_de88497bcca1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_continuous_dualNorm_d0655469d688
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_measurable_f92e47842fbb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceSectionMass_proof_139e377538c6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiffOn_log_dualNorm_a92d55d266bf


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
open scoped ContDiff Manifold
noncomputable section
open GroundTheory.Heights₂.Heights.SliceFormLelongCompact
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.SliceFormLelongCompact
theorem _root_.solution (hLI : LogIntegrable.Statement) (hCM : ChartMassCompact.Statement)
    (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (f : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ)) (hu : linForm u ∉ J)
    (h0 : ∀ x ∈ zeroSet J, x ≠ 0) (hf : SmoothNear (zeroSet J) f) (hfc : HasCompactSupport f)
    (hφ : ∀ i, SmoothNear (zeroSet J) (φ i)) :
    Tendsto (fun ε => varInt J (d + 1) (fsLogReg h u ε) (vecCons f φ)) (𝓝[>] 0)
      (𝓝 (varInt J (d + 1) (fun x => Real.log ‖linEval u x‖) (vecCons f φ) -
        varInt J (d + 1) (fun x => Real.log (h.dualNorm x)) (vecCons f φ))) := by
  unfold varInt
  split_ifs with hA
  swap
  · simp only [sub_zero]
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0))
  have hAf := hA.choose_spec
  unfold chartInt
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : Fin n → ℂ)
  have hψ : ∀ i, SmoothNear (zeroSet J) (vecCons f φ i) := fun i =>
    Fin.cases (by simpa using hf) (fun i => by simpa using hφ i) i
  have hcs : HasCompactSupport (vecCons f φ 0) := by simpa using hfc
  have hcN : ContinuousOn (fun x => Real.log (h.dualNorm x)) (zeroSet J) :=
    (contDiffOn_log_dualNorm h).continuousOn.mono fun x hx => h0 x hx
  have hmN : Measurable fun x : Fin n → ℂ => Real.log (h.dualNorm x) :=
    Real.measurable_log.comp (SliceCut.continuous_dualNorm h).measurable
  have hmU : Measurable fun x : Fin n → ℂ => Real.log ‖linEval u x‖ :=
    Real.measurable_log.comp (Continuous.measurable (by unfold linEval; fun_prop))
  have hmeas : ∀ w, Measurable w → Measurable (chartDens J hA.choose w (vecCons f φ)) := fun w hw =>
    (SheetSumMeasurable.proof n (d + 1) J hA.choose w _ hJ hdim hAf hw hψ).1
  have hI1 := hLI n (d + 1) J hA.choose u (vecCons f φ) R hJ hdim hAf hu hψ
  have hI2 := hCM n (d + 1) J hA.choose (fun x => 2 * |Real.log (h.dualNorm x)| + 1) (vecCons f φ) hJ hdim
    hAf ((hcN.abs.const_smul (2 : ℝ)).add continuousOn_const) hψ (Or.inr ⟨0, hcs⟩)
  have hIN := hCM n (d + 1) J hA.choose _ (vecCons f φ) hJ hdim hAf hcN hψ (Or.inr ⟨0, hcs⟩)
  have hIU : Integrable (chartAbsDens J hA.choose (fun x => Real.log ‖linEval u x‖) (vecCons f φ)) := by
    rwa [← chartAbsDens_indicator_eq _ _ 0 (by simpa using hR)]
  rw [← integral_sub (integrable_chartDens hAf (hmeas _ hmU) hIU)
    (integrable_chartDens hAf (hmeas _ hmN) hIN)]
  obtain ⟨P, hP, hPy⟩ := LelongRegularise.exists_poly_of_linEval_eq_zero hJ hAf hu
  have hgood : ∀ᵐ y : Fin (d + 1) → ℂ, ∀ x ∈ fibre J hA.choose y, linEval u x ≠ 0 := by
    filter_upwards [LelongRegularise.ae_eval_ne_zero P hP] with y hy x hx hx0
    exact hy (hPy y x hx hx0)
  refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ ((hI1.const_mul 2).add hI2) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε _
    exact (hmeas _ (measurable_fsLogReg h u ε)).aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT one_pos] with ε hε
    filter_upwards [hgood] with y hy
    exact norm_chartDens_fsLogReg_le h hAf φ hR h0 hε.1 hε.2 hy
  · filter_upwards [hgood] with y hy
    exact tendsto_chartDens_fsLogReg h hAf u _ h0 hy
end GroundTheory.Heights₂.Heights.SliceFormLelongCompact
