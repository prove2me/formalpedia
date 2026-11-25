-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_regMax_c2_pointwise_bound_0941e6435e3b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:53:38.766489+00:00
-- url     : https://prove2.me/submissions/97e003b4-127e-4d7b-9aa9-d141afa32c61

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_RegularizedMaxC2ExampleRealLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_norm_le_of_symm_diag_27609f9b2cf4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv2_sub_of_contDiffOn_acec6951921d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_abs_fderiv_regMax_apply_le_aa15b2597d97
import Theorems.Thm_ReciprocityTheory_AnForm_A_abs_regMax_le
import Theorems.Thm_ReciprocityTheory_AnForm_A_fderiv2_regMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_add_const
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_comp_fderiv2
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_fderiv_nonneg
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_fderiv_sum
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_one_fderiv2_bound
import Theorems.Thm_ReciprocityTheory_AnForm_A_two_le_inf
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open Filter Topology Metric
open ReciprocityTheory.AnForm.A (regMax regMax_contDiff regMax_add_const abs_regMax_le regMax_fderiv_sum
  regMax_fderiv_nonneg fderiv2_regMax regMax_one_fderiv2_bound regMax_comp_fderiv2 two_le_inf)
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι] [Nonempty ι]
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
theorem _root_.solution {U : Set E} (hU : IsOpen U) {f : E → ℝ} (hf : ContDiffOn ℝ 2 f U)
    {u : ι → E → ℝ} (hu : ∀ j, ContDiffOn ℝ 2 (u j) U) {η : ℝ} (hη : 0 < η) {C : ℝ}
    (hC : ∀ p : ι → ℝ, ‖fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) p‖ ≤ C / η) {z : E} (hz : z ∈ U)
    {s0 s1 s2 : ℝ} (h0 : ∀ j, |u j z - f z| ≤ s0)
    (h1 : ∀ j, ‖fderiv ℝ (u j) z - fderiv ℝ f z‖ ≤ s1)
    (h2 : ∀ j, ‖fderiv ℝ (fderiv ℝ (u j)) z - fderiv ℝ (fderiv ℝ f) z‖ ≤ s2) :
    |(regMax η (fun j => u j z) + η / 2) - f z| ≤ s0 + η ∧
      ‖fderiv ℝ (fun x => regMax η (fun j => u j x) + η / 2) z - fderiv ℝ f z‖ ≤ s1 ∧
      ‖fderiv ℝ (fderiv ℝ (fun x => regMax η (fun j => u j x) + η / 2)) z -
          fderiv ℝ (fderiv ℝ f) z‖ ≤ 2 * (C / η * s1 ^ 2 + s2) := by
  classical
  obtain ⟨j₀⟩ := ‹Nonempty ι›
  have hs0 : 0 ≤ s0 := (h0 j₀).trans' (abs_nonneg _)
  have hs1 : 0 ≤ s1 := (h1 j₀).trans' (norm_nonneg _)
  have hs2 : 0 ≤ s2 := (h2 j₀).trans'
    (norm_nonneg (fderiv ℝ (fderiv ℝ (u j₀)) z - fderiv ℝ (fderiv ℝ f) z))
  have hCη : 0 ≤ C / η :=
    (hC 0).trans' (norm_nonneg (fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) 0))
  have hdiff : ∀ {φ : E → ℝ}, ContDiffOn ℝ 2 φ U → ∀ y ∈ U, DifferentiableAt ℝ φ y :=
    fun hφ y hy => (hφ.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
  have hdiff2 : ∀ {φ : E → ℝ}, ContDiffOn ℝ 2 φ U → DifferentiableAt ℝ (fderiv ℝ φ) z :=
    fun hφ => ((hφ.contDiffAt (hU.mem_nhds hz)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  let b : ι → E → ℝ := fun j x => u j x - f x
  have hb : ∀ j, ContDiffOn ℝ 2 (b j) U := fun j => (hu j).sub hf
  have hbv : ContDiffOn ℝ 2 (fun x j => b j x) U := contDiffOn_pi.2 hb
  let g : E → ℝ := fun x => regMax η (fun j => b j x)
  have hg2 : ContDiffOn ℝ 2 g U :=
    ((regMax_contDiff (ι := ι) hη).of_le two_le_inf).comp_contDiffOn hbv
  have hval : ∀ x, regMax η (fun j => u j x) = g x + f x := by
    intro x
    have := regMax_add_const η (fun j => b j x) (f x)
    simpa [b, g] using this
  have hG : (fun x => regMax η (fun j => u j x) + η / 2) = fun x => g x + f x + η / 2 := by
    funext x
    rw [hval]
  have hDG : ∀ y ∈ U, fderiv ℝ (fun x => regMax η (fun j => u j x) + η / 2) y =
      fderiv ℝ g y + fderiv ℝ f y := by
    intro y hy
    rw [hG, fderiv_add_const]
    exact fderiv_add (hdiff hg2 y hy) (hdiff hf y hy)
  have hDb : ∀ j, fderiv ℝ (b j) z = fderiv ℝ (u j) z - fderiv ℝ f z := fun j =>
    fderiv_sub (hdiff (hu j) z hz) (hdiff hf z hz)
  have hgz : HasFDerivAt g ((fderiv ℝ (regMax (ι := ι) η) (fun j => b j z)).comp
      (ContinuousLinearMap.pi fun j => fderiv ℝ (b j) z)) z := by
    have hbz : HasFDerivAt (fun x j => b j x) (ContinuousLinearMap.pi fun j => fderiv ℝ (b j) z) z :=
      hasFDerivAt_pi.2 fun j => (hdiff (hb j) z hz).hasFDerivAt
    exact ((regMax_contDiff (ι := ι) hη).differentiable (by simp) _).hasFDerivAt.comp z hbz
  have hnb1 : ∀ v, ‖(fun j => fderiv ℝ (b j) z v)‖ ≤ s1 * ‖v‖ := by
    intro v
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    rw [hDb]
    exact ((fderiv ℝ (u j) z - fderiv ℝ f z).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (h1 j) (norm_nonneg v))
  refine ⟨?_, ?_, ?_⟩
  · rw [hval]
    have hm := abs_regMax_le hη.le (fun j => b j z)
    have hbn : ‖(fun j => b j z)‖ ≤ s0 :=
      (pi_norm_le_iff_of_nonneg hs0).2 fun j => by rw [Real.norm_eq_abs]; exact h0 j
    have e : g z + f z + η / 2 - f z = g z + η / 2 := by ring
    rw [e]
    calc |g z + η / 2| ≤ |g z| + |η / 2| := abs_add_le _ _
      _ ≤ s0 + η := by
        rw [abs_of_pos (by positivity : (0 : ℝ) < η / 2)]
        have : |g z| ≤ ‖(fun j => b j z)‖ + η / 2 := hm
        linarith
  · rw [hDG z hz, add_sub_cancel_right, hgz.fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ hs1 fun v => ?_
    rw [ContinuousLinearMap.comp_apply, Real.norm_eq_abs]
    exact (abs_fderiv_regMax_apply_le hη _ _).trans (hnb1 v)
  · have hD2G : fderiv ℝ (fderiv ℝ (fun x => regMax η (fun j => u j x) + η / 2)) z =
        fderiv ℝ (fderiv ℝ g) z + fderiv ℝ (fderiv ℝ f) z := by
      have h : fderiv ℝ (fun x => regMax η (fun j => u j x) + η / 2) =ᶠ[𝓝 z]
          fun y => fderiv ℝ g y + fderiv ℝ f y :=
        Filter.eventually_of_mem (hU.mem_nhds hz) hDG
      rw [h.fderiv_eq]
      exact fderiv_add (hdiff2 hg2) (hdiff2 hf)
    rw [hD2G, add_sub_cancel_right]
    have hsym : ∀ v w, fderiv ℝ (fderiv ℝ g) z v w = fderiv ℝ (fderiv ℝ g) z w v :=
      (hg2.contDiffAt (hU.mem_nhds hz)).isSymmSndFDerivAt (by simp)
    refine norm_le_of_symm_diag hsym (by positivity) fun v => ?_
    have key : fderiv ℝ (fderiv ℝ g) z v v =
        fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) (fun j => b j z) (fun j => fderiv ℝ (b j) z v)
            (fun j => fderiv ℝ (b j) z v) +
          fderiv ℝ (regMax (ι := ι) η) (fun j => b j z)
            (fun j => fderiv ℝ (fderiv ℝ (b j)) z v v) :=
      regMax_comp_fderiv2 hη hU hb hz v
    rw [key]
    have hr : ‖(fun j => fderiv ℝ (fderiv ℝ (b j)) z v v)‖ ≤ s2 * ‖v‖ ^ 2 := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
      have e : fderiv ℝ (fderiv ℝ (b j)) z =
          fderiv ℝ (fderiv ℝ (u j)) z - fderiv ℝ (fderiv ℝ f) z :=
        fderiv2_sub_of_contDiffOn hU (hu j) hf hz
      rw [e]
      calc ‖(fderiv ℝ (fderiv ℝ (u j)) z - fderiv ℝ (fderiv ℝ f) z) v v‖
          ≤ ‖fderiv ℝ (fderiv ℝ (u j)) z - fderiv ℝ (fderiv ℝ f) z‖ * ‖v‖ * ‖v‖ :=
            ContinuousLinearMap.le_opNorm₂ _ v v
        _ ≤ s2 * ‖v‖ * ‖v‖ := by gcongr; exact h2 j
        _ = s2 * ‖v‖ ^ 2 := by ring
    have hm1 := abs_fderiv_regMax_apply_le hη (fun j => b j z)
      (fun j => fderiv ℝ (fderiv ℝ (b j)) z v v)
    have hm2 : |fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) (fun j => b j z)
        (fun j => fderiv ℝ (b j) z v) (fun j => fderiv ℝ (b j) z v)| ≤ C / η * (s1 * ‖v‖) ^ 2 := by
      rw [← Real.norm_eq_abs]
      calc _ ≤ ‖fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) (fun j => b j z)‖ *
            ‖(fun j => fderiv ℝ (b j) z v)‖ * ‖(fun j => fderiv ℝ (b j) z v)‖ :=
            ContinuousLinearMap.le_opNorm₂ _ _ _
        _ ≤ C / η * (s1 * ‖v‖) * (s1 * ‖v‖) := by
            gcongr
            · exact hC _
            · exact hnb1 v
            · exact hnb1 v
        _ = C / η * (s1 * ‖v‖) ^ 2 := by ring
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ C / η * (s1 * ‖v‖) ^ 2 + s2 * ‖v‖ ^ 2 := add_le_add hm2 (hm1.trans hr)
      _ = (C / η * s1 ^ 2 + s2) * ‖v‖ ^ 2 := by ring
end GroundTheory.Heights₂.Heights.AnalyticLimit
