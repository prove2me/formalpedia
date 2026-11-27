-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LelongLimitOffZero_proof_5edde413a29d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:09:36.426559+00:00
-- url     : https://prove2.me/submissions/94f5f3be-ee2c-4b04-9ffd-93babfd305a9

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongLimitOffZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHessCCompPluri
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongLimitOffZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_hessC_half_log_normSq_add_1b30ac20ecb4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffGradient_proof_81aaa98bdfc1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOff_proof_fa25535eea0a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HessCCompPluri_proof_738153eeeb36
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_abs_chartDens_le_2f3f1c71cee6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_linEval_b27409562f54
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_maDens_cons_of_hessC_eq_smul_1613fdd029d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sheetSum_le_mul_0df1d0f6a4b5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_smoothNear_of_contDiff_8ca53b5543f3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_vecCons_comp_613af14c7f72
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood


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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm
open scoped ContDiff
namespace GroundTheory.Heights₂.Heights
namespace LelongLimitOffZero
theorem _root_.solution (hM : ChartMassCompact.Statement) : LelongLimitOffZero.Statement := by
  classical
  intro n d J u f φ hJ hdim hu hf hfc hφ hdisj
  unfold varInt
  split_ifs with hA
  swap
  · exact tendsto_const_nhds
  set A := hA.choose with hAdef
  have hAf : IsFiniteProjection J A := hA.choose_spec
  have hZc : IsClosed (zeroSet J) := by
    have : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | MvPolynomial.eval x q = 0} := by
      ext x; simp [zeroSet]
    rw [this]
    exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
  have hK : IsCompact (tsupport f ∩ zeroSet J) := hfc.isCompact.inter_right hZc
  have hu0 : ∀ x ∈ tsupport f ∩ zeroSet J, linEval u x ≠ 0 := fun x hx h0 =>
    Set.disjoint_left.1 hdisj hx.1 ⟨hx.2, h0⟩
  set q : (Fin n → ℂ) → ℝ := fun x => ‖linEval u x‖ ^ 2 with hq
  have hqc : ContDiff ℝ ∞ q := (contDiff_norm_sq ℝ).comp (contDiff_linEval u)
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ tsupport f ∩ zeroSet J, m ≤ q x := by
    rcases (tsupport f ∩ zeroSet J).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hqc.continuous.continuousOn
      exact ⟨q x₀, by have := hu0 x₀ hx₀; simp only [hq]; positivity, fun x hx => hmin hx⟩
  have hGi : Integrable (chartAbsDens J A f (vecCons q φ)) := by
    refine hM n (d + 1) J A f _ hJ hdim hAf hf.continuous.continuousOn (fun i => ?_) (Or.inl hfc)
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using smoothNear_of_contDiff (S := zeroSet J) hqc
    · simpa using hφ j
  have hb : ∀ ε : ℝ, 0 < ε → ∀ y, ‖chartDens J A f (vecCons (logReg u ε) φ) y‖ ≤
      ε / (2 * m ^ 2) * chartAbsDens J A f (vecCons q φ) y := by
    intro ε hε y
    rw [Real.norm_eq_abs]
    refine (abs_chartDens_le J A f _ y).trans ?_
    have hfin := (FibreBound.proof n (d + 1) J A hJ hdim hAf y).2.1
    unfold chartAbsDens
    refine sheetSum_le_mul hfin _ _ _ fun x hx s hs => ?_
    by_cases hfx : f x = 0
    · simp [hfx]
    have hxK : x ∈ tsupport f ∩ zeroSet J := ⟨subset_tsupport _ hfx, hx.1⟩
    obtain rfl : A *ᵥ x = y := hx.2
    obtain ⟨U, hU, hxU, hsd, hsx, -, -⟩ := hs
    have hsa : AnalyticAt ℂ s (A *ᵥ x) := analyticAt_pi_iff.2 fun i =>
      ReciprocityTheory.AnForm.Osgood.osgood _ U (fun z => s z i) hU (differentiableOn_pi.1 hsd i) _ hxU
    have hha : AnalyticAt ℂ (fun w => linEval u (s w)) (A *ᵥ x) := by
      unfold linEval
      exact Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul ((analyticAt_pi_iff.1 hsa) j)
    have hne : linEval u (s (A *ᵥ x)) ≠ 0 := by rw [hsx]; exact hu0 x hxK
    have hH0 := hessC_half_log_normSq_add (fun w => linEval u (s w)) _ hha hne hε
    simp only [hsx] at hH0
    have hH : hessC (logReg u ε ∘ s) (A *ᵥ x) =
        ((ε / (2 * (q x + ε) ^ 2) : ℝ) : ℂ) • hessC (q ∘ s) (A *ᵥ x) := hH0
    rw [vecCons_comp, vecCons_comp, maDens_cons_of_hessC_eq_smul (logReg u ε ∘ s) (q ∘ s) _ _ _ hH]
    have ha : m ≤ q x := hm x hxK
    have hc0 : 0 ≤ ε / (2 * (q x + ε) ^ 2) := by positivity
    have hc : ε / (2 * (q x + ε) ^ 2) ≤ ε / (2 * m ^ 2) :=
      div_le_div_of_nonneg_left hε.le (by positivity) (by nlinarith)
    calc |f x * (ε / (2 * (q x + ε) ^ 2) * maDens (Fin.cons (q ∘ s) fun k => φ k ∘ s) (A *ᵥ x))|
        = ε / (2 * (q x + ε) ^ 2) * |f x * maDens (Fin.cons (q ∘ s) fun k => φ k ∘ s) (A *ᵥ x)| := by
          rw [mul_left_comm, abs_mul, abs_of_nonneg hc0]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
  have hlim : Tendsto (fun ε : ℝ => ε / (2 * m ^ 2) * ∫ y, chartAbsDens J A f (vecCons q φ) y)
      (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => ε / (2 * m ^ 2) * ∫ y, chartAbsDens J A f (vecCons q φ) y) := by
      fun_prop
    exact tendsto_nhdsWithin_of_tendsto_nhds (hc.tendsto' 0 0 (by simp))
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  unfold chartInt
  rw [← integral_const_mul]
  exact norm_integral_le_of_norm_le (hGi.const_mul _) (Eventually.of_forall (hb ε hε))
end LelongLimitOffZero
end GroundTheory.Heights₂.Heights
