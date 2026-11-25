-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_proof_27abaefb27c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:58:56.863611+00:00
-- url     : https://prove2.me/submissions/84a3ba6a-fa2f-4580-9868-5ca3ff3b9aab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PHodgeDerivative
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_isOpen_punctured_dcac2e073bda
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_logLift_mem_9850b514c279
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_expCover_logLift_06dd0ae602f8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_imTau_eq_eaf25bdf3e9f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_one_add_sum_le_ee50fd91baad
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_one_le_chartRadius_c076bf66d5d4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_chartImag_entry_deriv_5fbd63be642a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_conj_sub_smul_one_f43216f942b1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_gram_posDef_179fcbfd6c04
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_inv_ge_of_le_f88fee38ae1c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_map_sub_smul_one_b0e909b5018b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_posDef_of_ge_c2392ab1fa43
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_posSemidef_map_ofReal_88bce7305c00
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_re_det_ofReal_smul_e0108b123d54
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_re_det_mono_86d278754b58
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_re_det_pos_df6c7fe9c329


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
open Metric Filter Topology Matrix
open GroundTheory.Heights₂.Heights.MCBounds GroundTheory.Heights₂.Heights.MCDet
open scoped ComplexOrder
noncomputable section
open HodgeDerivative
namespace GroundTheory.Heights₂.Heights.Regular
namespace HodgeDerivative
theorem _root_.solution (h0 : ImTauBounds.Statement) (h1 : Tau0Holomorphic.Statement)
    (hAn : AnalyticDerivBound.Statement) (hInv : InvEntryDeriv.Statement)
    (hLDG : LogDetGramDeriv.Statement) : HodgeDerivative.Statement := by
  intro n a g P
  obtain ⟨ρ, c, C, hρ0, hρ1, hc, hb⟩ := h0 n a g P
  obtain ⟨-, T0, hT⟩ := h1 n a g P
  set Bℝ : Fin a → Matrix (Fin g) (Fin g) ℝ := fun i => (P.B i).map (Int.cast : ℤ → ℝ) with hBℝ
  set Y : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℝ := chartImag P.a_le T0 Bℝ with hY
  have hKc : IsCompact (closedBall (0 : Fin n → ℂ) ρ) := isCompact_closedBall _ _
  have hKU : closedBall (0 : Fin n → ℂ) ρ ⊆ ball 0 1 := closedBall_subset_ball hρ1
  have hT0 := fun p q => hAn (fun y => T0 y p q) (ball 0 1) _ isOpen_ball (hT.1 p q) hKc hKU
  choose A hA0 hA using hT0
  set β : ℝ := ∑ i, ∑ p, ∑ q, |Bℝ i p q| with hβ
  set SA : ℝ := ∑ p, ∑ q, A p q with hSA
  set C0 : ℝ := SA + β with hC0
  have hAle : ∀ p q, A p q ≤ SA := fun p q =>
    (Finset.single_le_sum (f := fun q => A p q) (fun q _ => (hA0 p q).le) (Finset.mem_univ q)).trans
      (Finset.single_le_sum (f := fun p => ∑ q, A p q)
        (fun p _ => Finset.sum_nonneg fun q _ => (hA0 p q).le) (Finset.mem_univ p))
  have hBle : ∀ i p q, |Bℝ i p q| ≤ β := fun i p q =>
    ((Finset.single_le_sum (f := fun q => |Bℝ i p q|) (fun q _ => abs_nonneg _)
        (Finset.mem_univ q)).trans
      (Finset.single_le_sum (f := fun p => ∑ q, |Bℝ i p q|)
        (fun p _ => Finset.sum_nonneg fun q _ => abs_nonneg _) (Finset.mem_univ p))).trans
      (Finset.single_le_sum (f := fun i => ∑ p, ∑ q, |Bℝ i p q|)
        (fun i _ => Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => abs_nonneg _)
        (Finset.mem_univ i))
  have hβ0 : 0 ≤ β := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun p _ =>
    Finset.sum_nonneg fun q _ => abs_nonneg _
  have hSA0 : 0 ≤ SA := Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => (hA0 p q).le
  have hC00 : 0 ≤ C0 := add_nonneg hSA0 hβ0

  have hpt : ∀ z ∈ closedBall (0 : Fin n → ℂ) ρ, z ∈ puncturedChart P.a_le (ball 0 1) →
      (Y z - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef ∧
      ((max C 1 * chartRadius P.a_le z) • (1 : Matrix (Fin g) (Fin g) ℝ) - Y z).PosSemidef ∧
      (∀ p q, DifferentiableAt ℝ (fun y => Y y p q) z ∧
        ‖fderiv ℝ (fun y => Y y p q) z‖ ≤ C0 * (1 + ∑ i, ‖cuspCoord P.a_le z i‖⁻¹)) ∧
      (∀ p q, (fun y => P.hodge y p q) =ᶠ[𝓝 z] fun y => (Y y)⁻¹ p q) ∧
      (∀ (k : ℕ) (F : (Fin n → ℂ) → Matrix (Fin g) (Fin k) ℂ),
        (fun y => logDetGram (P.imTau y) (F y)) =ᶠ[𝓝 z] fun y => logDetGram (Y y) (F y)) := by
    intro z hzρ hz
    have hw := logLift_mem P.a_le hz
    have hexp := expCover_logLift P.a_le hz.2
    obtain ⟨hlow, hup⟩ := hb _ hw (by rw [hexp]; exact hzρ)
    have hIm : (P.τ (logLift a z)).map Complex.im = Y z := imTau_eq P hT hz
    rw [hIm] at hlow hup
    rw [hexp] at hup
    have hr1 := one_le_chartRadius P.a_le hz
    have hEq : ∀ᶠ y in 𝓝 z, P.imTau y = Y y :=
      Filter.eventually_of_mem ((isOpen_punctured P.a_le).mem_nhds hz) fun y hy => imTau_eq P hT hy
    refine ⟨hlow, ?_, fun p q => ?_, fun p q => hEq.mono fun y hy => ?_,
      fun k F => hEq.mono fun y hy => ?_⟩
    · have e : (max C 1 * chartRadius P.a_le z) • (1 : Matrix (Fin g) (Fin g) ℝ) - Y z =
          ((C * chartRadius P.a_le z) • (1 : Matrix (Fin g) (Fin g) ℝ) - Y z) +
            ((max C 1 - C) * chartRadius P.a_le z) • (1 : Matrix (Fin g) (Fin g) ℝ) := by
        rw [sub_mul, sub_smul]; abel
      rw [e]
      exact hup.add (PosSemidef.one.smul
        (mul_nonneg (sub_nonneg.mpr (le_max_left _ _)) (by linarith)))
    · obtain ⟨hd, hn⟩ := chartImag_entry_deriv P.a_le T0 Bℝ p q hz.2 (hA p q z hzρ).1
      refine ⟨hd, hn.trans ?_⟩
      have hS0 : 0 ≤ ∑ i, ‖cuspCoord P.a_le z i‖⁻¹ :=
        Finset.sum_nonneg fun i _ => inv_nonneg.mpr (norm_nonneg _)
      have h2 : ∑ i, |Bℝ i p q| * ‖cuspCoord P.a_le z i‖⁻¹ ≤
          β * ∑ i, ‖cuspCoord P.a_le z i‖⁻¹ := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hBle i p q) (inv_nonneg.mpr (norm_nonneg _))
      have h3 := (hA p q z hzρ).2.2
      have h4 := hAle p q
      nlinarith
    · simp only [PeriodPolydisc.hodge, hy]
    · simp only [hy]
  refine ⟨ρ, hρ0, hρ1, ⟨(g : ℝ) ^ 2 * c⁻¹ ^ 2 * C0 * (1 + a), fun z hzρ hz p q => ?_⟩, ?_⟩
  · obtain ⟨hYc, -, hYd, hH, -⟩ := hpt z hzρ hz
    have hi := hInv g Y z c _ hc hYc hYd p q
    rw [(hH p q).differentiableAt_iff, (hH p q).fderiv_eq]
    have hS0 : 0 ≤ ∑ i, ‖cuspCoord P.a_le z i‖⁻¹ :=
      Finset.sum_nonneg fun i _ => inv_nonneg.mpr (norm_nonneg _)
    have hk0 : 0 ≤ (g : ℝ) ^ 2 * c⁻¹ ^ 2 * C0 := by positivity
    have ha1 : (1 : ℝ) ≤ 1 + a := by linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
    refine ⟨hi.1, hi.2.trans ?_, hi.2.trans ?_⟩
    · rw [← mul_assoc, mul_assoc _ (1 + (a : ℝ))]
      exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by linarith) ha1) hk0
    · have := one_add_sum_le P.a_le hz
      rw [← mul_assoc, mul_assoc _ (1 + (a : ℝ))]
      exact mul_le_mul_of_nonneg_left this hk0
  · intro k F hF hrank
    obtain ⟨Kc, hKc0, hKmain⟩ := hLDG g k
    have hFb := fun j l => hAn (fun y => F y j l) (ball 0 1) _ isOpen_ball (hF j l) hKc hKU
    choose AF hAF0 hAF using hFb
    set aF : ℝ := ∑ j, ∑ l, AF j l with haF
    have hAFle : ∀ j l, AF j l ≤ aF := fun j l =>
      (Finset.single_le_sum (f := fun l => AF j l) (fun l _ => (hAF0 j l).le)
        (Finset.mem_univ l)).trans
        (Finset.single_le_sum (f := fun j => ∑ l, AF j l)
          (fun j _ => Finset.sum_nonneg fun l _ => (hAF0 j l).le) (Finset.mem_univ j))
    have haF0 : 0 ≤ aF := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => (hAF0 j l).le
    obtain ⟨δ, hδ, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧
        ∀ z ∈ closedBall (0 : Fin n → ℂ) ρ, δ ≤ ((F z)ᴴ * F z).det.re := by
      have hcont : ContinuousOn F (closedBall 0 ρ) := by
        rw [continuousOn_iff_continuous_domRestrict]
        exact continuous_matrix fun j l => ((hF j l).continuousOn.mono hKU).domRestrict
      have hc' : ContinuousOn (fun y => ((F y)ᴴ * F y).det.re) (closedBall 0 ρ) := by
        rw [continuousOn_iff_continuous_domRestrict] at hcont ⊢
        exact Complex.continuous_re.comp (hcont.matrix_conjTranspose.matrix_mul hcont).matrix_det
      obtain ⟨z0, hz0, hmin⟩ := hKc.exists_isMinOn ⟨0, mem_closedBall_self hρ0.le⟩ hc'
      exact ⟨_, re_det_pos (gram_posDef _ (hrank z0 (hKU hz0))), fun z hz => hmin hz⟩
    set C1 : ℝ := max C 1 with hC1def
    have hC1 : 0 < C1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    set W : ℝ := Kc * (1 + aF) ^ (2 * k) * (1 + c⁻¹) ^ (k + 1) * C1 ^ k / δ with hW
    have hW0 : 0 ≤ W := by positivity
    set Q : ℝ := W * (1 + C0) with hQ
    have hQ0 : 0 ≤ Q := by positivity
    have ha1 : (1 : ℝ) ≤ 1 + a := by linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
    refine ⟨max (Q * (1 + a)) k, fun z hzρ hz => ?_⟩
    obtain ⟨hYc, hYup, hYd, -, hL⟩ := hpt z hzρ hz
    have hr1 := one_le_chartRadius P.a_le hz
    set r := chartRadius P.a_le z with hr
    set S := ∑ i, ‖cuspCoord P.a_le z i‖⁻¹ with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => inv_nonneg.mpr (norm_nonneg _)
    have hYpd := posDef_of_ge hc hYc
    have hl : 0 < C1 * r := by positivity
    have hμle : (C1 * r)⁻¹ ^ k * δ ≤
        ((F z)ᴴ * (Y z)⁻¹.map (fun x : ℝ => (x : ℂ)) * F z).det.re := by
      have h1 := posSemidef_map_ofReal (inv_ge_of_le hl hYpd hYup)
      rw [map_sub_smul_one] at h1
      have h2 := h1.conjTranspose_mul_mul_same (F z)
      rw [conj_sub_smul_one] at h2
      have h3 : ((((C1 * r)⁻¹ : ℝ) : ℂ) • ((F z)ᴴ * F z)).PosSemidef :=
        (posSemidef_conjTranspose_mul_self (F z)).smul
          (Complex.zero_le_real.mpr (inv_nonneg.mpr hl.le))
      have := re_det_mono h3 h2
      simp only [RCLike.re_to_complex] at this
      rw [re_det_ofReal_smul] at this
      exact le_trans (mul_le_mul_of_nonneg_left (hδle z hzρ) (by positivity)) this
    have hFent : ∀ j l, DifferentiableAt ℝ (fun y => F y j l) z ∧ ‖F z j l‖ ≤ aF ∧
        ‖fderiv ℝ (fun y => F y j l) z‖ ≤ aF := fun j l =>
      ⟨(hAF j l z hzρ).1, (hAF j l z hzρ).2.1.trans (hAFle j l),
        (hAF j l z hzρ).2.2.trans (hAFle j l)⟩
    have hm := hKmain F Y z aF (C0 * (1 + S)) c ((C1 * r)⁻¹ ^ k * δ) hc (by positivity) haF0
      (by positivity) hFent hYd hYc hμle
    rw [(hL k F).differentiableAt_iff, (hL k F).fderiv_eq]

    have hX : Kc * (1 + aF) ^ (2 * k) * (1 + c⁻¹) ^ (k + 1) * (1 + C0 * (1 + S)) /
        ((C1 * r)⁻¹ ^ k * δ) ≤ Q * r ^ k * (1 + S) := by
      have e : Kc * (1 + aF) ^ (2 * k) * (1 + c⁻¹) ^ (k + 1) * (1 + C0 * (1 + S)) /
          ((C1 * r)⁻¹ ^ k * δ) = W * r ^ k * (1 + C0 * (1 + S)) := by
        rw [hW, inv_pow, mul_pow]
        field_simp
      rw [e, hQ, mul_assoc W (1 + C0), mul_comm (1 + C0), ← mul_assoc W, mul_assoc (W * r ^ k)]
      exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    have hCf : Q * (1 + a) ≤ max (Q * (1 + a)) k := le_max_left _ _
    have hQf : Q ≤ max (Q * (1 + a)) k := (le_mul_of_one_le_right hQ0 ha1).trans hCf
    have hrk : r ^ k ≤ r ^ (max (Q * (1 + a)) k) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hr1 (le_max_right _ _)
    have hrk0 : 0 ≤ r ^ k := by positivity
    refine ⟨hm.1, hm.2.trans (hX.trans ?_), hm.2.trans (hX.trans ?_)⟩
    · exact mul_le_mul_of_nonneg_right (mul_le_mul hQf hrk hrk0 (by linarith)) (by linarith)
    · have hE := one_add_sum_le P.a_le hz
      calc Q * r ^ k * (1 + S) ≤ Q * r ^ k * ((1 + a) * Real.exp (r / 2)) :=
            mul_le_mul_of_nonneg_left hE (by positivity)
        _ = Q * (1 + a) * r ^ k * Real.exp (r / 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul hCf hrk hrk0 (by linarith)) (Real.exp_pos _).le
end HodgeDerivative
end GroundTheory.Heights₂.Heights.Regular
