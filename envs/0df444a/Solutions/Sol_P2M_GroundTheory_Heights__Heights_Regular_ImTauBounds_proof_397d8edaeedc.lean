-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_ImTauBounds_proof_397d8edaeedc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:38:57.978933+00:00
-- url     : https://prove2.me/submissions/d166ed65-c7b7-45a2-825a-69a305f526a3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PImTauBounds
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_dot_self_nonneg_b78618d375ca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_quad_upper_core_c53c0b0b1192
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_quad_lower_core_dd44993edd4d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_im_tau_eq_524c6347d7ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_quad_add_sum_2f7b2a3f7c10

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Filter Topology
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
namespace ImTauBounds
theorem _root_.solution (h0 : Tau0Holomorphic.Statement) (h1 : KernelPositive.Statement) :
    ImTauBounds.Statement := by
  intro n a g P
  obtain ⟨hB, T0, hT0⟩ := h0 n a g P
  have hBpsd : ∀ i, (P.realB i).PosSemidef := hB
  have hBnn : ∀ i (v : Fin g → ℝ), 0 ≤ v ⬝ᵥ P.realB i *ᵥ v := fun i v => by
    simpa using (posSemidef_iff_dotProduct_mulVec.mp (hBpsd i)).2 v
  set S := ∑ i, P.realB i with hSdef
  have hSv : ∀ v : Fin g → ℝ, v ⬝ᵥ S *ᵥ v = ∑ i, v ⬝ᵥ P.realB i *ᵥ v := fun v => by
    rw [hSdef, Matrix.sum_mulVec, dotProduct_sum]
  have hS : S.PosSemidef := posSemidef_sum Finset.univ fun i _ => hBpsd i
  set Mz : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℝ := fun z => (T0 z).map Complex.im with hMz
  have hMc : ContinuousOn Mz (ball 0 1) := by
    refine continuousOn_pi.mpr fun p => continuousOn_pi.mpr fun q => ?_
    exact Complex.continuous_im.comp_continuousOn (hT0.1 p q).continuousOn
  have hK : IsCompact (closedBall (0 : Fin n → ℂ) (1 / 2)) := isCompact_closedBall _ _
  have hKW : closedBall (0 : Fin n → ℂ) (1 / 2) ⊆ ball 0 1 :=
    closedBall_subset_ball (by norm_num)
  have hpos : ∀ z ∈ closedBall (0 : Fin n → ℂ) (1 / 2), ∀ v : Fin g → ℝ, v ≠ 0 →
      S *ᵥ v = 0 → 0 < v ⬝ᵥ Mz z *ᵥ v := by
    intro z hz v hv hSv0
    refine h1 n a g P T0 hT0 v hv (fun i => ?_) z (hKW hz)
    have h := hSv v
    rw [hSv0, dotProduct_zero] at h
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hBnn j v)).mp h.symm i
      (Finset.mem_univ i)
    have := ((hBpsd i).dotProduct_mulVec_zero_iff v).mp
    simp only [star_trivial] at this
    exact this hi
  obtain ⟨L, ε, hε, hlow⟩ := quad_lower_core hK isOpen_ball hKW Mz hMc S hS hpos
  obtain ⟨A, hA0, hA⟩ := quad_upper_core hK Mz (hMc.mono hKW)
  have hBup : ∀ i, ∃ β : ℝ, 0 ≤ β ∧ ∀ v : Fin g → ℝ,
      v ⬝ᵥ P.realB i *ᵥ v ≤ β * (v ⬝ᵥ v) := by
    intro i
    obtain ⟨β, hβ0, hβ⟩ := quad_upper_core hK (fun _ => P.realB i) continuousOn_const
    exact ⟨β, hβ0, hβ 0 (mem_closedBall_self (by norm_num))⟩
  choose β hβ0 hβ using hBup
  refine ⟨min (1 / 2) (Real.exp (-(2 * Real.pi) * L)), ε, A + ∑ i, β i,
    lt_min (by norm_num) (Real.exp_pos _), lt_of_le_of_lt (min_le_left _ _) (by norm_num), hε, ?_⟩
  intro w hw hz
  have hzK : expCover a w ∈ closedBall (0 : Fin n → ℂ) (1 / 2) :=
    closedBall_subset_closedBall (min_le_left _ _) hz
  have hdec := P.im_tau_eq hT0 hw
  set z := expCover a w with hzdef
  set l : Fin a → ℝ := fun i => -(w (Fin.castLE P.a_le i)).re / (2 * Real.pi) with hl
  have hquad : ∀ v : Fin g → ℝ, v ⬝ᵥ (P.τ w).map Complex.im *ᵥ v =
      v ⬝ᵥ Mz z *ᵥ v + ∑ i, l i * (v ⬝ᵥ P.realB i *ᵥ v) := by
    intro v; rw [hdec]; exact quad_add_sum _ _ _ v
  have hzi : ∀ i : Fin a, z (Fin.castLE P.a_le i) = Complex.exp (w (Fin.castLE P.a_le i)) := by
    intro i; simp [hzdef, expCover, i.isLt]
  have hre : ∀ i : Fin a, (w (Fin.castLE P.a_le i)).re < 0 := hw.1
  have hnorm : ∀ i : Fin a,
      Real.exp (w (Fin.castLE P.a_le i)).re ≤ Real.exp (-(2 * Real.pi) * L) := by
    intro i
    have h1 : ‖z (Fin.castLE P.a_le i)‖ ≤ ‖z‖ := norm_le_pi_norm z _
    have h2 : ‖z‖ ≤ min (1 / 2) (Real.exp (-(2 * Real.pi) * L)) := by
      simpa [mem_closedBall, dist_zero_right] using hz
    rw [hzi, Complex.norm_exp] at h1
    exact h1.trans (h2.trans (min_le_right _ _))
  have hlL : ∀ i, L ≤ l i := by
    intro i
    have := Real.exp_le_exp.mp (hnorm i)
    show L ≤ -(w (Fin.castLE P.a_le i)).re / (2 * Real.pi)
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hterm : ∀ j : Fin a,
      Real.log (‖cuspCoord P.a_le z j‖ ^ 2)⁻¹ = -2 * (w (Fin.castLE P.a_le j)).re := by
    intro j
    rw [cuspCoord, hzi, Complex.norm_exp, Real.log_inv, Real.log_pow, Real.log_exp]
    push_cast; ring
  have hsum0 : 0 ≤ ∑ j, Real.log (‖cuspCoord P.a_le z j‖ ^ 2)⁻¹ :=
    Finset.sum_nonneg fun j _ => by rw [hterm j]; linarith [hre j]
  have hr1 : 1 ≤ chartRadius P.a_le z := by
    rw [chartRadius]
    have he : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
    linarith
  have hlr : ∀ i, l i ≤ chartRadius P.a_le z := by
    intro i
    rw [chartRadius]
    have hsum : -2 * (w (Fin.castLE P.a_le i)).re ≤
        ∑ j, Real.log (‖cuspCoord P.a_le z j‖ ^ 2)⁻¹ := by
      rw [← hterm i]
      exact Finset.single_le_sum (f := fun j => Real.log (‖cuspCoord P.a_le z j‖ ^ 2)⁻¹)
        (fun j _ => by rw [hterm j]; linarith [hre j]) (Finset.mem_univ i)
    have hli : l i ≤ -2 * (w (Fin.castLE P.a_le i)).re := by
      show -(w (Fin.castLE P.a_le i)).re / (2 * Real.pi) ≤ _
      rw [div_le_iff₀ (by positivity)]
      have := hre i
      nlinarith [Real.pi_gt_three]
    have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    linarith
  have hsymm : ((P.τ w).map Complex.im)ᵀ = (P.τ w).map Complex.im := by
    rw [← Matrix.transpose_map, P.symm w hw]
  refine ⟨?_, ?_⟩
  · rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun v => ?_⟩
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_smul,
        transpose_one, hsymm]
    · simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul]
      rw [hquad]
      have h1 := hlow z hzK v
      rw [hSv, Finset.mul_sum] at h1
      have h2 : ∑ i, L * (v ⬝ᵥ P.realB i *ᵥ v) ≤ ∑ i, l i * (v ⬝ᵥ P.realB i *ᵥ v) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hlL i) (hBnn i v)
      linarith
  · rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun v => ?_⟩
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_smul,
        transpose_one, hsymm]
    · simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul]
      rw [hquad]
      have hvv := dot_self_nonneg v
      have h1 := hA z hzK v
      have h2 : ∑ i, l i * (v ⬝ᵥ P.realB i *ᵥ v) ≤
          ∑ i, chartRadius P.a_le z * (β i * (v ⬝ᵥ v)) :=
        Finset.sum_le_sum fun i _ => mul_le_mul (hlr i) (hβ i v) (hBnn i v) (by linarith)
      have h3 : ∑ i, chartRadius P.a_le z * (β i * (v ⬝ᵥ v)) =
          chartRadius P.a_le z * (∑ i, β i) * (v ⬝ᵥ v) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      have h4 : A * (v ⬝ᵥ v) ≤ A * chartRadius P.a_le z * (v ⬝ᵥ v) := by
        have := mul_le_mul_of_nonneg_left hr1 (mul_nonneg hA0 hvv)
        nlinarith
      nlinarith
end ImTauBounds
end GroundTheory.Heights₂.Heights.Regular
