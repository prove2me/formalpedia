-- Prove2me | solution 1 for StochLinOpt.UpperBound.confidenceBall2_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T16:34:05.644265+00:00
-- url     : https://prove2.me/submissions/e86da9de-8f0f-433d-a088-c45a154f7ef9

/- Written by Codex. Reused helpers are credited to mrfancypants
(accepted submissions d48d5e68-5536-4955-b058-d3975985f0f8 and
34d450b7-57ec-4923-81fa-627230f83e2a) and Nickrobbins95
(accepted submission 028e111f-382d-40d0-8008-127228d5e6cf). -/
import Mathlib
import Definitions.Def_StochLinOpt_UpperBound_analysisQuantities
import Definitions.Def_StochLinOpt_UpperBound_confidenceBall2


/- Helpers credited to mrfancypants, accepted submission d48d5e68-5536-4955-b058-d3975985f0f8. -/

open Matrix

namespace StochLinOpt.UpperBound

lemma aux_ssq_posDef {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) : (designMatrix x t).PosDef := by
  unfold designMatrix
  refine Matrix.PosDef.one.add_posSemidef ?_
  refine Matrix.posSemidef_sum _ (fun τ _ => ?_)
  simpa using Matrix.posSemidef_vecMulVec_self_star (x τ)

lemma aux_ssq_succ {n : ℕ} (x : ℕ → Fin n → ℝ) {t : ℕ} (ht : 1 ≤ t) :
    designMatrix x (t+1) = designMatrix x t + vecMulVec (x t) (x t) := by
  unfold designMatrix
  rw [Finset.sum_Ico_succ_top ht, add_assoc]

lemma aux_ssq_det_succ {n : ℕ} (x : ℕ → Fin n → ℝ) {t : ℕ} (ht : 1 ≤ t) :
    (designMatrix x (t+1)).det =
      (designMatrix x t).det * (1 + x t ⬝ᵥ ((designMatrix x t)⁻¹ *ᵥ x t)) := by
  rw [aux_ssq_succ x ht, vecMulVec_eq Unit, det_add_replicateCol_mul_replicateRow]
  · congr 1
    rw [det_unique]
    simp [Matrix.mul_apply, replicateRow, replicateCol, mulVec, dotProduct, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  · exact (aux_ssq_posDef x t).det_pos.ne'.isUnit

lemma aux_ssq_quad_nonneg {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) :
    0 ≤ x t ⬝ᵥ ((designMatrix x t)⁻¹ *ᵥ x t) := by
  simpa using (aux_ssq_posDef x t).inv.posSemidef.dotProduct_mulVec_nonneg (x t)

lemma aux_ssq_width_sq {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) :
    width x t ^ 2 = x t ⬝ᵥ ((designMatrix x t)⁻¹ *ᵥ x t) := by
  unfold width
  exact Real.sq_sqrt (aux_ssq_quad_nonneg x t)

lemma aux_ssq_sum_log {n : ℕ} (x : ℕ → Fin n → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, Real.log (1 + width x t ^ 2) =
      Real.log (designMatrix x (T+1)).det := by
  induction T with
  | zero => simp [designMatrix]
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, aux_ssq_det_succ x (by omega : 1 ≤ k+1),
      Real.log_mul, aux_ssq_width_sq]
    · exact (aux_ssq_posDef x _).det_pos.ne'
    · have := aux_ssq_quad_nonneg x (k+1)
      linarith

lemma aux_ssq_trace_le {n : ℕ} (x : ℕ → Fin n → ℝ) (T : ℕ)
    (hx : ∀ t ∈ Finset.Icc 1 T, ∀ i, |x t i| ≤ 1) :
    (designMatrix x (T+1)).trace ≤ n * ((T:ℝ) + 1) := by
  unfold designMatrix
  rw [trace_add, trace_one, trace_sum]
  simp only [trace_vecMulVec, Fintype.card_fin]
  have h1 : ∀ τ ∈ Finset.Ico 1 (T+1), x τ ⬝ᵥ x τ ≤ n := by
    intro τ hτ
    have hτ' : τ ∈ Finset.Icc 1 T := by
      simp only [Finset.mem_Ico, Finset.mem_Icc] at hτ ⊢; omega
    unfold dotProduct
    calc ∑ i, x τ i * x τ i ≤ ∑ _i : Fin n, (1:ℝ) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have := hx τ hτ' i
          rw [abs_le] at this
          nlinarith
      _ = n := by simp
  have h2 := Finset.sum_le_sum h1
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h2
  have : ((T + 1 - 1 : ℕ) : ℝ) = T := by simp
  rw [this] at h2
  nlinarith

lemma aux_ssq_logdet_le {n : ℕ} (x : ℕ → Fin n → ℝ) (T : ℕ)
    (hx : ∀ t ∈ Finset.Icc 1 T, ∀ i, |x t i| ≤ 1) :
    Real.log (designMatrix x (T+1)).det ≤ n * Real.log ((T:ℝ) + 1) := by
  have hA := aux_ssq_posDef x (T+1)
  have htr := aux_ssq_trace_le x T hx
  have htr' : (designMatrix x (T+1)).trace = ∑ i, hA.isHermitian.eigenvalues i := by
    simpa using hA.isHermitian.trace_eq_sum_eigenvalues
  have hdet : (designMatrix x (T+1)).det = ∏ i, hA.isHermitian.eigenvalues i := by
    simpa using hA.isHermitian.det_eq_prod_eigenvalues
  have hpos : ∀ i, 0 < hA.isHermitian.eigenvalues i := fun i => hA.eigenvalues_pos i
  rw [hdet, Real.log_prod (fun i _ => (hpos i).ne')]
  have hc : (0:ℝ) < (T:ℝ) + 1 := by positivity
  have hle : ∀ i, Real.log (hA.isHermitian.eigenvalues i) ≤
      Real.log ((T:ℝ) + 1) + hA.isHermitian.eigenvalues i / ((T:ℝ) + 1) - 1 := by
    intro i
    have h := Real.log_le_sub_one_of_pos (div_pos (hpos i) hc)
    rw [Real.log_div (hpos i).ne' hc.ne'] at h
    linarith
  calc ∑ i, Real.log (hA.isHermitian.eigenvalues i)
      ≤ ∑ i, (Real.log ((T:ℝ) + 1) + hA.isHermitian.eigenvalues i / ((T:ℝ) + 1) - 1) :=
        Finset.sum_le_sum (fun i _ => hle i)
    _ = n * Real.log ((T:ℝ) + 1) + (∑ i, hA.isHermitian.eigenvalues i) / ((T:ℝ) + 1) - n := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_div]
        simp
    _ ≤ n * Real.log ((T:ℝ) + 1) := by
        rw [← htr']
        have : (designMatrix x (T+1)).trace / ((T:ℝ) + 1) ≤ n := by
          rw [div_le_iff₀ hc]; exact htr
        linarith

lemma aux_ssq_cs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (v y : Fin n → ℝ) :
    (v ⬝ᵥ y) ^ 2 ≤ (v ⬝ᵥ (A *ᵥ v)) * (y ⬝ᵥ (A⁻¹ *ᵥ y)) := by
  have hT : Aᵀ = A := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hA.isHermitian.eq
  have hsym : ∀ a b : Fin n → ℝ, a ⬝ᵥ (A *ᵥ b) = b ⬝ᵥ (A *ᵥ a) := by
    intro a b
    rw [dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_comm]
  have hpsd : ∀ w, 0 ≤ w ⬝ᵥ (A *ᵥ w) := fun w => by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg w
  set u := A⁻¹ *ᵥ y with hu
  have hyu : y = A *ᵥ u := by
    rw [hu, mulVec_mulVec, mul_nonsing_inv _ hA.det_pos.ne'.isUnit, one_mulVec]
  have e1 : v ⬝ᵥ y = v ⬝ᵥ (A *ᵥ u) := by rw [← hyu]
  have e2 : y ⬝ᵥ u = u ⬝ᵥ (A *ᵥ u) := by
    rw [dotProduct_comm]; exact congrArg (fun z => u ⬝ᵥ z) hyu
  rw [e1, e2]
  have hq : ∀ s : ℝ, 0 ≤ (u ⬝ᵥ (A *ᵥ u)) * (s * s) + (-2 * (v ⬝ᵥ (A *ᵥ u))) * s +
      v ⬝ᵥ (A *ᵥ v) := by
    intro s
    have h := hpsd (v - s • u)
    simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul] at h
    rw [hsym u v] at h
    nlinarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith

lemma aux_ssq_par {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (a b : Fin n → ℝ) :
    (a - b) ⬝ᵥ (A *ᵥ (a - b)) ≤ 2 * (a ⬝ᵥ (A *ᵥ a)) + 2 * (b ⬝ᵥ (A *ᵥ b)) := by
  have h : 0 ≤ (a + b) ⬝ᵥ (A *ᵥ (a + b)) := by
    simpa using hA.dotProduct_mulVec_nonneg (a + b)
  simp only [mulVec_add, mulVec_sub, add_dotProduct, dotProduct_add, sub_dotProduct,
    dotProduct_sub] at h ⊢
  linarith

lemma aux_ssq_beta_mono {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {s t : ℕ} (hs : 1 ≤ s)
    (hst : s ≤ t) : beta n δ s ≤ beta n δ t := by
  unfold beta
  have hs' : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hst' : (s:ℝ) ≤ t := by exact_mod_cast hst
  have h1 : 0 ≤ Real.log s := Real.log_nonneg hs'
  have h2 : Real.log s ≤ Real.log t := Real.log_le_log (by linarith) hst'
  have h1' : 0 ≤ Real.log t := le_trans h1 h2
  have h3 : 0 < Real.log ((s:ℝ)^2/δ) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hδ]; nlinarith
  have h4 : Real.log ((s:ℝ)^2/δ) ≤ Real.log ((t:ℝ)^2/δ) :=
    Real.log_le_log (by positivity) (by gcongr)
  have hn : (0:ℝ) ≤ 128 * (n:ℝ) := by positivity
  apply max_le_max
  · exact mul_le_mul (mul_le_mul_of_nonneg_left h2 hn) h4 h3.le (mul_nonneg hn h1')
  · have : 0 ≤ 8 / 3 * Real.log ((s:ℝ)^2/δ) := by positivity
    exact pow_le_pow_left₀ this (by linarith) 2

lemma aux_ssq_min_log {u : ℝ} (hu : 0 ≤ u) : min u 1 ≤ 2 * Real.log (1 + u) := by
  rcases le_or_gt u 1 with h | h
  · rw [min_eq_left h]
    have h1 := Real.one_sub_inv_le_log_of_pos (by linarith : (0:ℝ) < 1 + u)
    have h2 : u / 2 ≤ 1 - (1 + u)⁻¹ := by
      rw [show 1 - (1 + u)⁻¹ = u / (1 + u) by field_simp; ring]
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith
    linarith
  · rw [min_eq_right h.le]
    have h1 := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log (1 + u) := Real.log_le_log (by norm_num) (by linarith)
    norm_num at h1
    linarith


end StochLinOpt.UpperBound

/- Matrix rank-one update helpers credited to Nickrobbins95, accepted OFUL submission 028e111f-382d-40d0-8008-127228d5e6cf. -/
set_option autoImplicit false
namespace ConfBallMatrix
open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_symm_dot {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ} (hA : Aᵀ = A) (v w : Fin d → ℝ) :
    v ⬝ᵥ A *ᵥ w = w ⬝ᵥ A *ᵥ v := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hA, dotProduct_comm]

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_vecMulVec_mulVec {d : ℕ} (x u : Fin d → ℝ) :
    vecMulVec x x *ᵥ u = (x ⬝ᵥ u) • x := by
  ext i
  simp [mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_comm, mul_left_comm]

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_posdef_transpose {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) : Vᵀ = V := by
  have := hV.isHermitian
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  exact this

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_inv_transpose {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) : (V⁻¹)ᵀ = V⁻¹ := by
  rw [transpose_nonsing_inv, e5_posdef_transpose hV]

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_det_unit {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) : IsUnit V.det :=
  isUnit_iff_ne_zero.mpr hV.det_pos.ne'

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_mulVec_inv {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : IsUnit V.det) (v : Fin d → ℝ) :
    V *ᵥ (V⁻¹ *ᵥ v) = v := by
  rw [mulVec_mulVec, mul_nonsing_inv _ hV, one_mulVec]

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_inv_mulVec {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : IsUnit V.det) (v : Fin d → ℝ) :
    V⁻¹ *ᵥ (V *ᵥ v) = v := by
  rw [mulVec_mulVec, nonsing_inv_mul _ hV, one_mulVec]

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_a_nonneg {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) (x : Fin d → ℝ) :
    0 ≤ x ⬝ᵥ V⁻¹ *ᵥ x := by
  have := hV.inv.posSemidef.dotProduct_mulVec_nonneg x
  simpa using this

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_det_step {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) (x : Fin d → ℝ) :
    (V + vecMulVec x x).det = V.det * (1 + x ⬝ᵥ V⁻¹ *ᵥ x) := by
  rw [vecMulVec_eq Unit, det_add_replicateCol_mul_replicateRow (e5_det_unit hV)]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, replicateRow_apply,
    replicateCol_apply, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_quad_step {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) (x S : Fin d → ℝ)
    (e : ℝ) :
    (S + e • x) ⬝ᵥ (V + vecMulVec x x)⁻¹ *ᵥ (S + e • x) =
      S ⬝ᵥ V⁻¹ *ᵥ S + (2 * e * (x ⬝ᵥ V⁻¹ *ᵥ S) + e ^ 2 * (x ⬝ᵥ V⁻¹ *ᵥ x)
        - (x ⬝ᵥ V⁻¹ *ᵥ S) ^ 2) / (1 + x ⬝ᵥ V⁻¹ *ᵥ x) := by
  set a := x ⬝ᵥ V⁻¹ *ᵥ x with ha_def
  set b := x ⬝ᵥ V⁻¹ *ᵥ S with hb_def
  have ha : 0 ≤ a := e5_a_nonneg hV x
  have h1a : (1 + a) ≠ 0 := by positivity
  have hdet : IsUnit V.det := e5_det_unit hV
  have hdet' : IsUnit (V + vecMulVec x x).det := by
    rw [e5_det_step hV]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero hV.det_pos.ne' h1a)
  set u := V⁻¹ *ᵥ S with hu
  set w := V⁻¹ *ᵥ x with hw
  set cc := (e - b) / (1 + a) with hcc
  have hxu : x ⬝ᵥ u = b := rfl
  have hxw : x ⬝ᵥ w = a := rfl
  have hSw : S ⬝ᵥ w = b := by
    rw [hw, hb_def, e5_symm_dot (e5_inv_transpose hV)]
  have h1 : (V + vecMulVec x x) *ᵥ (u + cc • w) = S + e • x := by
    rw [add_mulVec, e5_vecMulVec_mulVec, mulVec_add, mulVec_smul, hu, hw, e5_mulVec_inv hdet,
      e5_mulVec_inv hdet, ← hu, ← hw, dotProduct_add, dotProduct_smul, hxu, hxw, smul_eq_mul,
      add_assoc, ← add_smul]
    congr 2
    rw [hcc]
    field_simp
    ring
  have key : (V + vecMulVec x x)⁻¹ *ᵥ (S + e • x) = u + cc • w := by
    rw [← h1, e5_inv_mulVec hdet']
  rw [key, add_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct, dotProduct_smul,
    dotProduct_smul, smul_dotProduct, hSw, hxu, hxw]
  simp only [smul_eq_mul]
  rw [hcc]
  field_simp
  ring


open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_meas_det {Ω : Type*} [MeasurableSpace Ω] {n : Type*} [Fintype n] [DecidableEq n]
    {M : Ω → Matrix n n ℝ} (hM : ∀ i j, Measurable fun ω => M ω i j) :
    Measurable fun ω => (M ω).det := by
  simp_rw [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact Finset.measurable_sum _ fun σ _ =>
    measurable_const.mul (Finset.measurable_prod _ fun i _ => hM _ _)

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_meas_inv {Ω : Type*} [MeasurableSpace Ω] {n : Type*} [Fintype n] [DecidableEq n]
    {M : Ω → Matrix n n ℝ} (hM : ∀ i j, Measurable fun ω => M ω i j) (i j : n) :
    Measurable fun ω => (M ω)⁻¹ i j := by
  simp_rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv',
    Matrix.adjugate_apply]
  refine (e5_meas_det hM).inv.mul (e5_meas_det fun k l => ?_)
  simp only [updateRow_apply]
  by_cases h : k = j
  · simp only [h, if_true]; exact measurable_const
  · simp only [h, if_false]; exact hM k l

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_meas_quad {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {M : Ω → Matrix (Fin d) (Fin d) ℝ} (hM : ∀ i j, Measurable fun ω => M ω i j)
    {v w : Ω → Fin d → ℝ} (hv : Measurable v) (hw : Measurable w) :
    Measurable fun ω => v ω ⬝ᵥ M ω *ᵥ w ω := by
  simp only [dotProduct, mulVec]
  refine Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hv).mul ?_
  exact Finset.measurable_sum _ fun j _ => (hM i j).mul ((measurable_pi_apply j).comp hw)


end ConfBallMatrix

set_option autoImplicit false
open Matrix ConfBallMatrix
namespace StochLinOpt.UpperBound

noncomputable def cbScore {n : ℕ} (μ : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    (t : ℕ) : Fin n → ℝ :=
  (∑ τ ∈ Finset.Ico 1 t, ℓ τ • x τ) - designMatrix x t *ᵥ μ

lemma cbScore_inv {n : ℕ} (μ : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ) (t : ℕ) :
    (designMatrix x t)⁻¹ *ᵥ cbScore μ x ℓ t = muHat x ℓ t - μ := by
  unfold cbScore muHat
  rw [mulVec_sub,e5_inv_mulVec (aux_ssq_posDef x t).det_pos.ne'.isUnit]

lemma cb_zScore {n : ℕ} (μ : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ) (t : ℕ) :
    zStat μ x ℓ t = cbScore μ x ℓ t ⬝ᵥ ((designMatrix x t)⁻¹ *ᵥ cbScore μ x ℓ t) := by
  rw [cbScore_inv]
  unfold zStat
  rw [← cbScore_inv μ x ℓ t,e5_mulVec_inv (aux_ssq_posDef x t).det_pos.ne'.isUnit,
    dotProduct_comm]

lemma cbScore_succ {n : ℕ} (μ : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    {t : ℕ} (ht : 1 ≤ t) :
    cbScore μ x ℓ (t+1) = cbScore μ x ℓ t + (ℓ t - μ ⬝ᵥ x t) • x t := by
  unfold cbScore
  rw [Finset.sum_Ico_succ_top ht,aux_ssq_succ x ht,add_mulVec,e5_vecMulVec_mulVec,
    dotProduct_comm (x t) μ,sub_smul]
  abel

lemma cb_zStep {n : ℕ} (μ : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    {t : ℕ} (ht : 1 ≤ t) :
    zStat μ x ℓ (t+1) ≤ zStat μ x ℓ t
      + 2 * ((ℓ t - μ ⬝ᵥ x t) * (x t ⬝ᵥ (muHat x ℓ t - μ)) / (1 + width x t ^ 2))
      + (ℓ t - μ ⬝ᵥ x t)^2 * width x t^2 / (1 + width x t^2) := by
  rw [cb_zScore μ x ℓ (t+1),cbScore_succ μ x ℓ ht,aux_ssq_succ x ht,
    e5_quad_step (aux_ssq_posDef x t),cb_zScore μ x ℓ t,cbScore_inv,←aux_ssq_width_sq]
  have hp : 0 < 1 + width x t^2 := by positivity
  have hn : 0 ≤ (x t ⬝ᵥ (muHat x ℓ t - μ))^2 / (1 + width x t^2) := by positivity
  have he : (2 * (ℓ t - μ ⬝ᵥ x t) * (x t ⬝ᵥ (muHat x ℓ t - μ))
       + (ℓ t - μ ⬝ᵥ x t)^2 * width x t^2
       - (x t ⬝ᵥ (muHat x ℓ t - μ))^2) / (1 + width x t^2) =
       2 * ((ℓ t - μ ⬝ᵥ x t) * (x t ⬝ᵥ (muHat x ℓ t - μ)) / (1 + width x t^2))
       + (ℓ t - μ ⬝ᵥ x t)^2 * width x t^2 / (1 + width x t^2)
       - (x t ⬝ᵥ (muHat x ℓ t - μ))^2 / (1 + width x t^2) := by ring
  rw [he]
  linarith

lemma cb_mu_norm {n : ℕ} (D : Set (Fin n → ℝ)) (μ : Fin n → ℝ)
    (hD_basis : ∀ i : Fin n, (Pi.single i (1 : ℝ) : Fin n → ℝ) ∈ D)
    (hμD : ∀ y ∈ D, |μ ⬝ᵥ y| ≤ 1) : μ ⬝ᵥ μ ≤ n := by
  have hi : ∀ i, |μ i| ≤ 1 := by
    intro i
    simpa using hμD _ (hD_basis i)
  calc μ ⬝ᵥ μ ≤ ∑ _i : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have h := hi i
        rw [abs_le] at h
        nlinarith
    _ = n := by simp

lemma cb_z_initial {n : ℕ} (μ : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    {t : ℕ} (ht : t ≤ 1) : zStat μ x ℓ t = μ ⬝ᵥ μ := by
  have hempty : Finset.Ico 1 t = ∅ := Finset.Ico_eq_empty_of_le ht
  simp [zStat,muHat,designMatrix,hempty]

lemma cb_zStat_checked {n : ℕ} (D : Set (Fin n → ℝ)) (μ : Fin n → ℝ)
    (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    (hD_basis : ∀ i : Fin n, (Pi.single i (1 : ℝ) : Fin n → ℝ) ∈ D)
    (hμD : ∀ y ∈ D, |μ ⬝ᵥ y| ≤ 1) (t : ℕ) :
    zStat μ x ℓ t ≤ n
      + 2 * ∑ τ ∈ Finset.Ico 1 t,
          (ℓ τ - μ ⬝ᵥ x τ) * (x τ ⬝ᵥ (muHat x ℓ τ - μ)) / (1 + width x τ ^ 2)
      + ∑ τ ∈ Finset.Ico 1 t,
          (ℓ τ - μ ⬝ᵥ x τ) ^ 2 * width x τ ^ 2 / (1 + width x τ ^ 2) := by
  induction t with
  | zero => simpa [cb_z_initial μ x ℓ (by omega : 0 ≤ 1)] using cb_mu_norm D μ hD_basis hμD
  | succ t ih =>
    by_cases ht : 1 ≤ t
    · rw [Finset.sum_Ico_succ_top ht,Finset.sum_Ico_succ_top ht]
      have hs := cb_zStep μ x ℓ ht
      linarith
    · have ht0 : t = 0 := by omega
      subst t
      simpa [cb_z_initial μ x ℓ (by omega : 1 ≤ 1)] using cb_mu_norm D μ hD_basis hμD

end StochLinOpt.UpperBound

open MeasureTheory ProbabilityTheory Matrix ConfBallMatrix
set_option autoImplicit false
namespace StochLinOpt.UpperBound

noncomputable def cbCoeff {n : ℕ} (δ : ℝ) (μ : Fin n → ℝ) (x : ℕ → Fin n → ℝ)
    (ℓ : ℕ → ℝ) (t : ℕ) : ℝ :=
  2 * escapeInd δ μ x ℓ t * (x t ⬝ᵥ (muHat x ℓ t - μ)) / (1 + width x t^2)

lemma cb_increment_eq {n : ℕ} (δ : ℝ) (μ : Fin n → ℝ) (x : ℕ → Fin n → ℝ)
    (ℓ : ℕ → ℝ) (t : ℕ) :
    mIncrement δ μ x ℓ t = (ℓ t - μ ⬝ᵥ x t) * cbCoeff δ μ x ℓ t := by
  unfold mIncrement cbCoeff;ring

lemma cb_beta_nonneg {n : ℕ} (δ : ℝ) (t : ℕ) : 0 ≤ beta n δ t :=
  le_max_of_le_right (sq_nonneg _)

lemma cb_coeff_sq {n : ℕ} (δ : ℝ) (μ : Fin n → ℝ) (x : ℕ → Fin n → ℝ)
    (ℓ : ℕ → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    cbCoeff δ μ x ℓ t^2 ≤ 4 * beta n δ t * width x t^2 / (1 + width x t^2)^2 := by
  classical
  by_cases h : ∀ τ ∈ Finset.Icc 1 t, zStat μ x ℓ τ ≤ beta n δ τ
  · have hz := h t (Finset.mem_Icc.mpr ⟨ht,le_rfl⟩)
    have hcs := aux_ssq_cs (designMatrix x t) (aux_ssq_posDef x t)
      (muHat x ℓ t - μ) (x t)
    rw [dotProduct_comm (muHat x ℓ t - μ) (x t),←aux_ssq_width_sq] at hcs
    change (x t ⬝ᵥ (muHat x ℓ t - μ))^2 ≤ zStat μ x ℓ t * width x t^2 at hcs
    have hcs' := hcs.trans (mul_le_mul_of_nonneg_right hz (sq_nonneg _))
    simp only [cbCoeff,escapeInd,if_pos h,mul_one,div_pow,mul_pow]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    nlinarith
  · simp only [cbCoeff,escapeInd,if_neg h,mul_zero,zero_mul,zero_div,zero_pow (by decide : (2 : ℕ) ≠ 0)]
    have hb := cb_beta_nonneg (n := n) δ t
    positivity

lemma cb_coeff_bound {n : ℕ} (δ : ℝ) (μ : Fin n → ℝ) (x : ℕ → Fin n → ℝ)
    (ℓ : ℕ → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    |cbCoeff δ μ x ℓ t| ≤ Real.sqrt (beta n δ t) := by
  have h := cb_coeff_sq δ μ x ℓ t ht
  have hb := cb_beta_nonneg (n := n) δ t
  have hp : 0 < 1 + width x t^2 := by positivity
  have hratio : 4 * width x t^2 / (1 + width x t^2)^2 ≤ 1 := by
    rw [div_le_iff₀ (sq_pos_of_pos hp)]
    nlinarith [sq_nonneg (width x t^2 - 1)]
  have hmul := mul_le_mul_of_nonneg_left hratio hb
  have hc : cbCoeff δ μ x ℓ t^2 ≤ beta n δ t := by
    calc _ ≤ _ := h
      _ = beta n δ t * (4 * width x t^2 / (1 + width x t^2)^2) := by ring
      _ ≤ _ := by simpa using hmul
  have hs := Real.sq_sqrt hb
  have ha := abs_nonneg (cbCoeff δ μ x ℓ t)
  have hab := sq_abs (cbCoeff δ μ x ℓ t)
  have hr := Real.sqrt_nonneg (beta n δ t)
  nlinarith

end StochLinOpt.UpperBound

set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory ConfBallMatrix
namespace StochLinOpt.UpperBound

lemma cb_meas_design {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (x : ℕ → Ω → Fin n → ℝ) (t : ℕ)
    (hx : ∀ s ∈ Finset.Ico 1 t, Measurable (x s)) (i j : Fin n) :
    Measurable (fun ω => designMatrix (fun s => x s ω) t i j) := by
  simp only [designMatrix,Matrix.add_apply,Matrix.sum_apply,vecMulVec_apply]
  exact measurable_const.add (Finset.measurable_sum _ fun s hs =>
    ((measurable_pi_apply i).comp (hx s hs)).mul ((measurable_pi_apply j).comp (hx s hs)))

lemma cb_meas_hat {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (x : ℕ → Ω → Fin n → ℝ) (ℓ : ℕ → Ω → ℝ) (t : ℕ)
    (hx : ∀ s ∈ Finset.Ico 1 t, Measurable (x s))
    (hℓ : ∀ s ∈ Finset.Ico 1 t, Measurable (ℓ s)) :
    Measurable (fun ω => muHat (fun s => x s ω) (fun s => ℓ s ω) t) := by
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [muHat,mulVec,dotProduct,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  exact Finset.measurable_sum _ fun j _ =>
    (e5_meas_inv (cb_meas_design x t hx) i j).mul (Finset.measurable_sum _ fun s hs =>
      (hℓ s hs).mul ((measurable_pi_apply j).comp (hx s hs)))

lemma cb_meas_width {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (x : ℕ → Ω → Fin n → ℝ) (t : ℕ)
    (hx : ∀ s ∈ Finset.Ico 1 t, Measurable (x s)) (hxt : Measurable (x t)) :
    Measurable (fun ω => width (fun s => x s ω) t) := by
  unfold width
  exact (e5_meas_quad (fun i j => e5_meas_inv (cb_meas_design x t hx) i j) hxt hxt).sqrt

lemma cb_meas_z {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → ℝ) (x : ℕ → Ω → Fin n → ℝ) (ℓ : ℕ → Ω → ℝ) (t : ℕ)
    (hx : ∀ s ∈ Finset.Ico 1 t, Measurable (x s))
    (hℓ : ∀ s ∈ Finset.Ico 1 t, Measurable (ℓ s)) :
    Measurable (fun ω => zStat μ (fun s => x s ω) (fun s => ℓ s ω) t) := by
  unfold zStat
  have hh : Measurable (fun ω => muHat (fun s => x s ω) (fun s => ℓ s ω) t - μ) :=
    (cb_meas_hat x ℓ t hx hℓ).sub measurable_const
  exact e5_meas_quad (cb_meas_design x t hx) hh hh

lemma cb_coeff_meas {Ω : Type*} {mΩ : MeasurableSpace Ω} {n : ℕ}
    (𝓕 : Filtration ℕ mΩ) (δ : ℝ) (μ : Fin n → ℝ)
    (x : ℕ → Ω → Fin n → ℝ) (ℓ : ℕ → Ω → ℝ)
    (hx : ∀ t, 1 ≤ t → Measurable[𝓕 t] (x t))
    (hℓ : ∀ t, 1 ≤ t → Measurable[𝓕 (t+1)] (ℓ t)) (t : ℕ) (ht : 1 ≤ t) :
    Measurable[𝓕 t] (fun ω => cbCoeff δ μ (fun s => x s ω) (fun s => ℓ s ω) t) := by
  have hxp : ∀ s ∈ Finset.Ico 1 t, Measurable[𝓕 t] (x s) := by
    intro s hs
    obtain ⟨hs1,hst⟩ := Finset.mem_Ico.mp hs
    exact (hx s hs1).mono (𝓕.mono (by omega)) le_rfl
  have hℓp : ∀ s ∈ Finset.Ico 1 t, Measurable[𝓕 t] (ℓ s) := by
    intro s hs
    obtain ⟨hs1,hst⟩ := Finset.mem_Ico.mp hs
    exact (hℓ s hs1).mono (𝓕.mono (by omega)) le_rfl
  have hh := @cb_meas_hat Ω (𝓕 t) n x ℓ t hxp hℓp
  have hw := @cb_meas_width Ω (𝓕 t) n x t hxp (hx t ht)
  have hz : ∀ τ ∈ Finset.Icc 1 t, Measurable[𝓕 t]
      (fun ω => zStat μ (fun s => x s ω) (fun s => ℓ s ω) τ) := by
    intro τ hτ
    exact @cb_meas_z Ω (𝓕 t) n μ x ℓ τ
      (fun s hs => hxp s (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hs).1,
        lt_of_lt_of_le (Finset.mem_Ico.mp hs).2 (Finset.mem_Icc.mp hτ).2⟩))
      (fun s hs => hℓp s (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hs).1,
        lt_of_lt_of_le (Finset.mem_Ico.mp hs).2 (Finset.mem_Icc.mp hτ).2⟩))
  have hset : MeasurableSet[𝓕 t] {ω | ∀ τ ∈ Finset.Icc 1 t,
      zStat μ (fun s => x s ω) (fun s => ℓ s ω) τ ≤ beta n δ τ} := by
    have hsets : MeasurableSet[𝓕 t] (⋂ τ ∈ Finset.Icc 1 t,
        {ω | zStat μ (fun s => x s ω) (fun s => ℓ s ω) τ ≤ beta n δ τ}) :=
      Finset.measurableSet_biInter _ (fun τ hτ => measurableSet_le (hz τ hτ) measurable_const)
    convert hsets using 1
    ext ω
    simp
  have he : Measurable[𝓕 t] (fun ω => escapeInd δ μ (fun s => x s ω) (fun s => ℓ s ω) t) := by
    unfold escapeInd
    exact Measurable.ite hset measurable_const measurable_const
  have hb : Measurable[𝓕 t] (fun ω => x t ω ⬝ᵥ
      (muHat (fun s => x s ω) (fun s => ℓ s ω) t - μ)) := by
    unfold dotProduct
    exact Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp (hx t ht)).mul
      ((measurable_pi_apply i).comp (hh.sub measurable_const))
  unfold cbCoeff
  exact ((measurable_const.mul he).mul hb).div (measurable_const.add (hw.pow_const 2))

end StochLinOpt.UpperBound

open MeasureTheory ProbabilityTheory Matrix
set_option autoImplicit false
namespace StochLinOpt.UpperBound

lemma cb_ratio_log {r : ℝ} (hr : 0 ≤ r) : r / (1+r)^2 ≤ Real.log (1+r) := by
  have hp : 0 < 1+r := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hp
  have he : 1-(1+r)⁻¹ = r/(1+r) := by field_simp;ring
  rw [he] at hlog
  apply le_trans _ hlog
  rw [div_le_div_iff₀ (sq_pos_of_pos hp) hp]
  exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg r] : 1+r ≤ (1+r)^2) hr

lemma cb_logsum_bound {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) (ht : 1 ≤ t)
    (hx : ∀ s ∈ Finset.Ico 1 t, ∀ i, |x s i| ≤ 1) :
    ∑ s ∈ Finset.Ico 1 t, Real.log (1+width x s^2) ≤ n * Real.log t := by
  have he : Finset.Ico 1 t = Finset.Icc 1 (t-1) := by ext s;simp;omega
  have ht' : t-1+1=t := by omega
  have h := aux_ssq_logdet_le x (t-1) (by simpa [←he] using hx)
  rw [he,aux_ssq_sum_log,ht']
  have hcast : ((t-1 : ℕ) : ℝ)+1 = (t : ℝ) := by exact_mod_cast ht'
  simpa only [ht',hcast] using h

lemma cb_coeff_sum_bound {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (μ : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ) (t : ℕ) (ht : 1 ≤ t)
    (hx : ∀ s ∈ Finset.Ico 1 t, ∀ i, |x s i| ≤ 1) :
    ∑ s ∈ Finset.Ico 1 t, cbCoeff δ μ x ℓ s^2 ≤ 4 * beta n δ t * n * Real.log t := by
  have hB := cb_beta_nonneg (n := n) δ t
  calc ∑ s ∈ Finset.Ico 1 t, cbCoeff δ μ x ℓ s^2
      ≤ ∑ s ∈ Finset.Ico 1 t, 4 * beta n δ t * Real.log (1+width x s^2) := by
        apply Finset.sum_le_sum
        intro s hs
        have hs1 := (Finset.mem_Ico.mp hs).1
        have hst : s ≤ t := (Finset.mem_Ico.mp hs).2.le
        have hb := aux_ssq_beta_mono (n := n) hδ hδ1 hs1 hst
        calc _ ≤ 4 * beta n δ s * width x s^2 / (1+width x s^2)^2 := cb_coeff_sq δ μ x ℓ s hs1
          _ ≤ 4 * beta n δ t * width x s^2 / (1+width x s^2)^2 := by gcongr
          _ = 4 * beta n δ t * (width x s^2 / (1+width x s^2)^2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (cb_ratio_log (sq_nonneg _)) (by positivity)
    _ = 4 * beta n δ t * ∑ s ∈ Finset.Ico 1 t, Real.log (1+width x s^2) := by rw [Finset.mul_sum]
    _ ≤ 4 * beta n δ t * (n * Real.log t) :=
      mul_le_mul_of_nonneg_left (cb_logsum_bound x t ht hx) (by positivity)
    _ = _ := by ring

lemma cb_increment_properties {n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℕ mΩ)
    (δ : ℝ) (μ : Fin n → ℝ) (x : ℕ → Ω → Fin n → ℝ) (ℓ : ℕ → Ω → ℝ)
    (hx : ∀ t, 1 ≤ t → Measurable[𝓕 t] (x t))
    (hℓ : ∀ t, 1 ≤ t → Measurable[𝓕 (t+1)] (ℓ t))
    (hℓb : ∀ t, 1 ≤ t → ∀ ω, |ℓ t ω| ≤ 1)
    (hηb : ∀ t, 1 ≤ t → ∀ ω, |ℓ t ω - μ ⬝ᵥ x t ω| ≤ 1)
    (hmean : ∀ t, 1 ≤ t → P[ℓ t | 𝓕 t] =ᵐ[P] fun ω => μ ⬝ᵥ x t ω)
    (t : ℕ) (ht : 1 ≤ t) :
    let M := fun ω => mIncrement δ μ (fun s => x s ω) (fun s => ℓ s ω) t
    let C := fun ω => cbCoeff δ μ (fun s => x s ω) (fun s => ℓ s ω) t
    Measurable[𝓕 (t+1)] M ∧ Integrable M P ∧ Integrable (fun ω => M ω^2) P ∧
      P[M | 𝓕 t] =ᵐ[P] 0 ∧ (P[fun ω => M ω^2 | 𝓕 t] ≤ᵐ[P] (fun ω => C ω^2)) ∧
      ∀ ω, |M ω| ≤ Real.sqrt (beta n δ t) := by
  let E : Ω → ℝ := fun ω => ℓ t ω - μ ⬝ᵥ x t ω
  let C : Ω → ℝ := fun ω => cbCoeff δ μ (fun s => x s ω) (fun s => ℓ s ω) t
  let M : Ω → ℝ := fun ω => mIncrement δ μ (fun s => x s ω) (fun s => ℓ s ω) t
  have hc : Measurable[𝓕 t] C := cb_coeff_meas 𝓕 δ μ x ℓ hx hℓ t ht
  have hu : Measurable[𝓕 t] (fun ω => μ ⬝ᵥ x t ω) := by
    unfold dotProduct
    exact Finset.measurable_sum _ fun i _ => measurable_const.mul ((measurable_pi_apply i).comp (hx t ht))
  have he : Measurable[𝓕 (t+1)] E := (hℓ t ht).sub (hu.mono (𝓕.mono (Nat.le_succ _)) le_rfl)
  have hMeq : M = E * C := by funext ω;exact cb_increment_eq δ μ (fun s => x s ω) (fun s => ℓ s ω) t
  have hm : Measurable[𝓕 (t+1)] M := by rw [hMeq];exact he.mul (hc.mono (𝓕.mono (Nat.le_succ _)) le_rfl)
  have hcbd : ∀ ω, |C ω| ≤ Real.sqrt (beta n δ t) := fun ω => cb_coeff_bound δ μ _ _ t ht
  have hmbd : ∀ ω, |M ω| ≤ Real.sqrt (beta n δ t) := by
    intro ω
    rw [hMeq,Pi.mul_apply,abs_mul]
    calc _ ≤ 1 * Real.sqrt (beta n δ t) := mul_le_mul (hηb t ht ω) (hcbd ω) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hi : Integrable M P := Integrable.of_bound (hm.mono (𝓕.le _) le_rfl).aestronglyMeasurable
    (Real.sqrt (beta n δ t)) (Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hmbd ω))
  have hsqbd : ∀ ω, |M ω^2| ≤ beta n δ t := by
    intro ω
    rw [abs_of_nonneg (sq_nonneg _)]
    have h := pow_le_pow_left₀ (abs_nonneg _) (hmbd ω) 2
    rwa [sq_abs,Real.sq_sqrt (cb_beta_nonneg δ t)] at h
  have hi2 : Integrable (fun ω => M ω^2) P := Integrable.of_bound
    ((hm.mono (𝓕.le _) le_rfl).pow_const 2).aestronglyMeasurable (beta n δ t)
    (Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hsqbd ω))
  have hci2 : Integrable (fun ω => C ω^2) P := Integrable.of_bound
    ((hc.mono (𝓕.le _) le_rfl).pow_const 2).aestronglyMeasurable (beta n δ t)
    (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have h := pow_le_pow_left₀ (abs_nonneg _) (hcbd ω) 2
      rwa [sq_abs,Real.sq_sqrt (cb_beta_nonneg δ t)] at h))
  have hei : Integrable E P := Integrable.of_bound (he.mono (𝓕.le _) le_rfl).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hηb t ht ω))
  have hli : Integrable (ℓ t) P := Integrable.of_bound ((hℓ t ht).mono (𝓕.le _) le_rfl).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hℓb t ht ω))
  have hui : Integrable (fun ω => μ ⬝ᵥ x t ω) P := by
    have huE : (fun ω => μ ⬝ᵥ x t ω) = ℓ t - E := by funext ω;dsimp [E];ring
    rw [huE];exact hli.sub hei
  have hezero : P[E | 𝓕 t] =ᵐ[P] 0 := by
    have hs := condExp_sub hli hui (m := 𝓕 t)
    rw [condExp_of_stronglyMeasurable (𝓕.le t) hu.stronglyMeasurable hui] at hs
    filter_upwards [hs,hmean t ht] with ω h1 h2
    change P[E | 𝓕 t] ω = 0
    change P[E | 𝓕 t] ω = P[ℓ t | 𝓕 t] ω - μ ⬝ᵥ x t ω at h1
    rw [h1,h2];ring
  have hmzero : P[M | 𝓕 t] =ᵐ[P] 0 := by
    have hp := condExp_mul_of_stronglyMeasurable_right hc.stronglyMeasurable
      (show Integrable (E*C) P from hMeq ▸ hi) hei
    rw [←hMeq] at hp
    filter_upwards [hp,hezero] with ω h1 h2
    change P[E | 𝓕 t] ω = 0 at h2
    change P[M | 𝓕 t] ω = 0
    simpa only [Pi.mul_apply,h2,zero_mul] using h1
  have hvar : P[fun ω => M ω^2 | 𝓕 t] ≤ᵐ[P] fun ω => C ω^2 := by
    have hp := condExp_mono (m := 𝓕 t) hi2 hci2 (Filter.Eventually.of_forall (fun ω => by
      change M ω^2 ≤ C ω^2
      rw [hMeq,Pi.mul_apply,mul_pow]
      have h := hηb t ht ω
      have hs : E ω^2 ≤ 1 := by
        have h' := pow_le_pow_left₀ (abs_nonneg (E ω)) h 2
        simpa only [sq_abs,one_pow] using h'
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (sq_nonneg (C ω))))
    rw [condExp_of_stronglyMeasurable (𝓕.le t) (hc.pow_const 2).stronglyMeasurable hci2] at hp
    exact hp
  exact ⟨hm,hi,hi2,hmzero,hvar,hmbd⟩

end StochLinOpt.UpperBound

set_option autoImplicit false
open Matrix
namespace StochLinOpt.UpperBound

lemma cb_log_positive {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {t : ℕ} (ht : 1 ≤ t) :
    0 < Real.log ((t : ℝ)^2/δ) := by
  apply Real.log_pos
  rw [lt_div_iff₀ hδ]
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  nlinarith

lemma cb_beta_positive {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    {t : ℕ} (ht : 1 ≤ t) : 0 < beta n δ t := by
  have hL := cb_log_positive hδ hδ1 ht
  exact lt_of_lt_of_le (sq_pos_of_pos (by positivity : 0 < 8/3*Real.log ((t : ℝ)^2/δ))) (le_max_right _ _)

lemma cb_freedman_numeric {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    {t : ℕ} (ht : 2 ≤ t) :
    Real.exp (-(beta n δ t/2)^2 /
      (2*(4*beta n δ t*n*Real.log t)+2*(beta n δ t/2)*Real.sqrt (beta n δ t)/3))
      ≤ δ/(t : ℝ)^2 := by
  let B := beta n δ t
  let L := Real.log ((t : ℝ)^2/δ)
  have hB : 0 < B := cb_beta_positive hδ hδ1 (by omega)
  have hL : 0 < L := cb_log_positive hδ hδ1 (by omega)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ht' : (1 : ℝ) < t := by exact_mod_cast ht
  have hlog : 0 < Real.log t := Real.log_pos ht'
  have hfirst : 128*n*Real.log t*L ≤ B := le_max_left _ _
  have hsecond : (8/3*L)^2 ≤ B := le_max_right _ _
  have hs0 := Real.sqrt_nonneg B
  have hs := Real.sq_sqrt hB.le
  have hsbound : 8/3*L ≤ Real.sqrt B := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hfirst hB.le
  have h2 := mul_le_mul_of_nonneg_left hsbound hs0
  have h3 := mul_le_mul_of_nonneg_left h2 hB.le
  have hD : 0 < 2*(4*B*n*Real.log t)+2*(B/2)*Real.sqrt B/3 := by positivity
  have hkey : L ≤ (B/2)^2/(2*(4*B*n*Real.log t)+2*(B/2)*Real.sqrt B/3) := by
    rw [le_div_iff₀ hD]
    nlinarith
  have he : Real.exp (-(B/2)^2/(2*(4*B*n*Real.log t)+2*(B/2)*Real.sqrt B/3)) ≤ Real.exp (-L) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    exact neg_le_neg hkey
  have heq : Real.exp (-L) = δ/(t : ℝ)^2 := by
    rw [Real.exp_neg]
    dsimp [L]
    rw [Real.exp_log (by positivity)]
    field_simp
  exact he.trans_eq heq

lemma cb_beta_drift {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    {t : ℕ} (ht : 2 ≤ t) : n + n * Real.log t ≤ beta n δ t / 2 := by
  have ht' : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hlt : 1/2 < Real.log t := lt_of_lt_of_le (by linarith [Real.log_two_gt_d9])
    (Real.log_le_log (by norm_num) ht')
  have htpos : (0 : ℝ) < t := by linarith
  have hL : 2*Real.log t ≤ Real.log ((t : ℝ)^2/δ) := by
    rw [Real.log_div (pow_ne_zero _ htpos.ne') hδ.ne',Real.log_pow]
    have hld : Real.log δ < 0 := Real.log_neg hδ hδ1
    norm_num only [Nat.cast_ofNat]
    linarith
  have h1 : 128*n*Real.log t*Real.log ((t : ℝ)^2/δ) ≤ beta n δ t := le_max_left _ _
  have h2 := mul_le_mul_of_nonneg_left hL (show 0 ≤ 128*(n : ℝ)*Real.log t by positivity)
  have h3 : 1+Real.log t ≤ 128*(Real.log t)^2 := by nlinarith [sq_nonneg (Real.log t-1)]
  have h4 := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith

end StochLinOpt.UpperBound

/- Freedman bound credited to mrfancypants, accepted submission 34d450b7-57ec-4923-81fa-627230f83e2a. -/

open MeasureTheory

namespace StochLinOpt.UpperBound

lemma aux_fr_H (x : ℝ) : 0 ≤ (x - 1) * Real.exp x + 1 := by
  have h := Real.add_one_le_exp (-x)
  have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have hp := Real.exp_pos x
  nlinarith

lemma aux_fr_G_deriv (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y - 2) * Real.exp y + y + 2) ((x - 1) * Real.exp x + 1) x := by
  have h1 : HasDerivAt (fun y : ℝ => y - 2) 1 x := (hasDerivAt_id x).sub_const 2
  have h2 := (h1.mul (Real.hasDerivAt_exp x)).add (hasDerivAt_id x)
  have h3 := h2.add_const 2
  exact h3.congr_deriv (by ring)

lemma aux_fr_G_mono : Monotone (fun y : ℝ => (y - 2) * Real.exp y + y + 2) := by
  apply monotone_of_deriv_nonneg
  · intro x; exact (aux_fr_G_deriv x).differentiableAt
  · intro x; rw [(aux_fr_G_deriv x).deriv]; exact aux_fr_H x

lemma aux_fr_F_deriv (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 2 / 2 - (1 - y / 3) * (Real.exp y - 1 - y))
      (((x - 2) * Real.exp x + x + 2) / 3) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
    simpa using (hasDerivAt_pow 2 x).div_const 2
  have h2 : HasDerivAt (fun y : ℝ => 1 - y / 3) (-(1/3)) x := by
    simpa using ((hasDerivAt_id x).div_const 3).const_sub 1
  have h3 : HasDerivAt (fun y : ℝ => Real.exp y - 1 - y) (Real.exp x - 1) x :=
    ((Real.hasDerivAt_exp x).sub_const 1).sub (hasDerivAt_id x)
  have := h1.sub (h2.mul h3)
  exact this.congr_deriv (by ring)

lemma aux_fr_exp_ineq (y : ℝ) : (1 - y / 3) * (Real.exp y - 1 - y) ≤ y ^ 2 / 2 := by
  set F : ℝ → ℝ := fun y => y ^ 2 / 2 - (1 - y / 3) * (Real.exp y - 1 - y) with hF
  have hG0 : ((0:ℝ) - 2) * Real.exp 0 + 0 + 2 = 0 := by simp
  have hcont : Continuous F := by
    rw [hF]; fun_prop
  have hdiff : Differentiable ℝ F := fun x => (aux_fr_F_deriv x).differentiableAt
  have hF0 : F 0 = 0 := by simp [hF]
  suffices 0 ≤ F y by simp only [hF] at this; linarith
  rcases le_total y 0 with hy | hy
  · have hanti : AntitoneOn F (Set.Iic 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Iic 0) hcont.continuousOn hdiff.differentiableOn
      intro x hx
      rw [interior_Iic] at hx
      rw [(aux_fr_F_deriv x).deriv]
      have := aux_fr_G_mono (le_of_lt (Set.mem_Iio.mp hx))
      simp only at this
      linarith
    have := hanti (Set.mem_Iic.mpr hy) (Set.mem_Iic.mpr le_rfl) hy
    linarith
  · have hmono : MonotoneOn F (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont.continuousOn hdiff.differentiableOn
      intro x hx
      rw [interior_Ici] at hx
      rw [(aux_fr_F_deriv x).deriv]
      have := aux_fr_G_mono (le_of_lt (Set.mem_Ioi.mp hx))
      simp only at this
      linarith
    have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy
    linarith

lemma aux_fr_pw (l b x : ℝ) (hl : 0 < l) (hd : 0 < 1 - l * b / 3) (hx : x ≤ b) :
    Real.exp (l * x) ≤ 1 + l * x + l ^ 2 / (2 * (1 - l * b / 3)) * x ^ 2 := by
  have h1 := aux_fr_exp_ineq (l * x)
  have h2 : 0 ≤ Real.exp (l * x) - 1 - l * x := by
    have := Real.add_one_le_exp (l * x); linarith
  have h3 : l * x ≤ l * b := mul_le_mul_of_nonneg_left hx hl.le
  have h4 : (1 - l * b / 3) * (Real.exp (l * x) - 1 - l * x) ≤ (l * x) ^ 2 / 2 := by
    calc (1 - l * b / 3) * (Real.exp (l * x) - 1 - l * x)
        ≤ (1 - l * x / 3) * (Real.exp (l * x) - 1 - l * x) := by
          apply mul_le_mul_of_nonneg_right _ h2; linarith
      _ ≤ _ := h1
  have h5 : Real.exp (l * x) - 1 - l * x ≤ l ^ 2 / (2 * (1 - l * b / 3)) * x ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  linarith


lemma aux_fr_int_condExp {Ω : Type*} {m mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (hm : m ≤ mΩ) (Y Z : Ω → ℝ) (hY : StronglyMeasurable[m] Y)
    (hYZ : Integrable (fun ω => Y ω * Z ω) P) (hZ : Integrable Z P) :
    ∫ ω, Y ω * Z ω ∂P = ∫ ω, Y ω * (P[Z | m]) ω ∂P := by
  calc ∫ ω, Y ω * Z ω ∂P = ∫ ω, (P[Y * Z | m]) ω ∂P := (integral_condExp hm).symm
    _ = ∫ ω, (Y * P[Z | m]) ω ∂P :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hY hYZ hZ)
    _ = _ := rfl

lemma aux_fr_main {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (T : ℕ) (b : ℝ)
    (hmeas : ∀ i ∈ Finset.Icc 1 T, Measurable[𝓕 (i + 1)] (X i))
    (hint : ∀ i ∈ Finset.Icc 1 T, Integrable (X i) P)
    (hint_sq : ∀ i ∈ Finset.Icc 1 T, Integrable (fun ω => X i ω ^ 2) P)
    (hmds : ∀ i ∈ Finset.Icc 1 T, P[X i | 𝓕 i] =ᵐ[P] 0)
    (hb : ∀ i ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, X i ω ≤ b)
    (l c : ℝ) (hl : 0 < l) (hc : 0 ≤ c)
    (hpw : ∀ x ≤ b, Real.exp (l * x) ≤ 1 + l * x + c * x ^ 2)
    (V : ℕ → Ω → ℝ) (hV : ∀ i, V i = P[fun ω' => X i ω' ^ 2 | 𝓕 i]) :
    ∀ k ≤ T, Integrable (fun ω => Real.exp (l * ∑ i ∈ Finset.Icc 1 k, X i ω
        - c * ∑ i ∈ Finset.Icc 1 k, V i ω)) P ∧
      ∫ ω, Real.exp (l * ∑ i ∈ Finset.Icc 1 k, X i ω
        - c * ∑ i ∈ Finset.Icc 1 k, V i ω) ∂P ≤ 1 := by
  have hVsm : ∀ i, StronglyMeasurable[𝓕 i] (V i) := fun i => by
    rw [hV]; exact stronglyMeasurable_condExp
  have hVint : ∀ i, Integrable (V i) P := fun i => by rw [hV]; exact integrable_condExp
  have hVnn : ∀ i, 0 ≤ᵐ[P] V i := fun i => by
    rw [hV]; exact condExp_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
  have hgood : ∀ᵐ ω ∂P, ∀ i ∈ Finset.Icc 1 T, X i ω ≤ b ∧ 0 ≤ V i ω := by
    rw [Filter.eventually_all_finset]
    intro i hi
    filter_upwards [hb i hi, hVnn i] with ω h1 h2
    exact ⟨h1, h2⟩
  have hXm0 : ∀ i ∈ Finset.Icc 1 T, Measurable (X i) := fun i hi =>
    (hmeas i hi).mono (𝓕.le _) le_rfl
  have hWm : ∀ k, Measurable[𝓕 k] (fun ω => ∑ i ∈ Finset.Icc 1 k, V i ω) := fun k =>
    Finset.measurable_sum _ (fun i hi =>
      (hVsm i).measurable.mono (𝓕.mono (by simp at hi; omega)) le_rfl)
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    obtain ⟨ihint, ihle⟩ := ih (by omega)
    have hk1 : k + 1 ∈ Finset.Icc 1 T := Finset.mem_Icc.mpr ⟨by omega, hk⟩
    have hSm : Measurable[𝓕 (k+1)] (fun ω => ∑ i ∈ Finset.Icc 1 k, X i ω) :=
      Finset.measurable_sum _ (fun i hi =>
        (hmeas i (by simp at hi ⊢; omega)).mono (𝓕.mono (by simp at hi; omega)) le_rfl)
    set Y : Ω → ℝ := fun ω => Real.exp (l * ∑ i ∈ Finset.Icc 1 k, X i ω
        - c * ∑ i ∈ Finset.Icc 1 k, V i ω - c * V (k+1) ω) with hYdef
    have hYm : StronglyMeasurable[𝓕 (k+1)] Y := by
      have : Measurable[𝓕 (k+1)] Y := by
        apply Real.measurable_exp.comp
        exact ((hSm.const_mul l).sub (((hWm k).mono (𝓕.mono (Nat.le_succ k)) le_rfl).const_mul c)).sub
          ((hVsm (k+1)).measurable.const_mul c)
      exact this.stronglyMeasurable
    have hYae : AEStronglyMeasurable Y P := (hYm.mono (𝓕.le _)).aestronglyMeasurable
    have hYbd : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ Real.exp (l * ∑ i ∈ Finset.Icc 1 k, b) := by
      filter_upwards [hgood] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have h1 : ∑ i ∈ Finset.Icc 1 k, X i ω ≤ ∑ i ∈ Finset.Icc 1 k, b :=
        Finset.sum_le_sum (fun i hi => (hω i (by simp at hi ⊢; omega)).1)
      have h2 : 0 ≤ ∑ i ∈ Finset.Icc 1 k, V i ω :=
        Finset.sum_nonneg (fun i hi => (hω i (by simp at hi ⊢; omega)).2)
      have h3 : 0 ≤ V (k+1) ω := (hω (k+1) hk1).2
      nlinarith [mul_le_mul_of_nonneg_left h1 hl.le, mul_nonneg hc h2, mul_nonneg hc h3]
    have hYint : Integrable Y P := Integrable.of_bound hYae _ hYbd
    have hEm : Measurable (fun ω => Real.exp (l * X (k+1) ω)) :=
      Real.measurable_exp.comp ((hXm0 _ hk1).const_mul l)
    have hEint : Integrable (fun ω => Real.exp (l * X (k+1) ω)) P := by
      refine Integrable.of_bound hEm.aestronglyMeasurable (Real.exp (l * b)) ?_
      filter_upwards [hgood] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hω (k+1) hk1).1 hl.le)
    have hfun : (fun ω => Real.exp (l * ∑ i ∈ Finset.Icc 1 (k+1), X i ω
        - c * ∑ i ∈ Finset.Icc 1 (k+1), V i ω)) =
        fun ω => Y ω * Real.exp (l * X (k+1) ω) := by
      funext ω
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), hYdef,
        ← Real.exp_add]
      congr 1; ring
    have hMint : Integrable (fun ω => Y ω * Real.exp (l * X (k+1) ω)) P :=
      hEint.bdd_mul hYae hYbd
    rw [hfun]
    refine ⟨hMint, ?_⟩
    have hYX : Integrable (fun ω => Y ω * X (k+1) ω) P := (hint _ hk1).bdd_mul hYae hYbd
    have hYX2 : Integrable (fun ω => Y ω * X (k+1) ω ^ 2) P := (hint_sq _ hk1).bdd_mul hYae hYbd
    have hYV : Integrable (fun ω => Y ω * V (k+1) ω) P := (hVint _).bdd_mul hYae hYbd
    have hYX0 : ∫ ω, Y ω * X (k+1) ω ∂P = 0 := by
      rw [aux_fr_int_condExp P (𝓕.le (k+1)) Y (X (k+1)) hYm hYX (hint _ hk1)]
      rw [integral_congr_ae (g := fun _ => (0:ℝ)) ?_]
      · simp
      filter_upwards [hmds _ hk1] with ω hω
      simp [hω]
    have hYX2V : ∫ ω, Y ω * X (k+1) ω ^ 2 ∂P = ∫ ω, Y ω * V (k+1) ω ∂P := by
      rw [aux_fr_int_condExp P (𝓕.le (k+1)) Y (fun ω => X (k+1) ω ^ 2) hYm hYX2 (hint_sq _ hk1),
        hV]
    have hYpos : ∀ ω, 0 < Y ω := fun ω => Real.exp_pos _
    have i1 : Integrable (fun ω => Y ω + l * (Y ω * X (k+1) ω)) P := hYint.add (hYX.const_mul l)
    have i2 : Integrable (fun ω => Y ω + l * (Y ω * X (k+1) ω) + c * (Y ω * X (k+1) ω ^ 2)) P :=
      i1.add (hYX2.const_mul c)
    have i3 : Integrable (fun ω => Y ω + c * (Y ω * V (k+1) ω)) P := hYint.add (hYV.const_mul c)
    calc ∫ ω, Y ω * Real.exp (l * X (k+1) ω) ∂P
        ≤ ∫ ω, (Y ω + l * (Y ω * X (k+1) ω) + c * (Y ω * X (k+1) ω ^ 2)) ∂P := by
          apply integral_mono_ae hMint i2
          filter_upwards [hgood] with ω hω
          have := mul_le_mul_of_nonneg_left (hpw _ (hω (k+1) hk1).1) (hYpos ω).le
          linarith
      _ = ∫ ω, Y ω ∂P + l * ∫ ω, Y ω * X (k+1) ω ∂P + c * ∫ ω, Y ω * X (k+1) ω ^ 2 ∂P := by
          have e1 : ∫ ω, (Y ω + l * (Y ω * X (k+1) ω) + c * (Y ω * X (k+1) ω ^ 2)) ∂P =
              ∫ ω, (Y ω + l * (Y ω * X (k+1) ω)) ∂P + ∫ ω, c * (Y ω * X (k+1) ω ^ 2) ∂P :=
            integral_add i1 (hYX2.const_mul c)
          have e2 : ∫ ω, (Y ω + l * (Y ω * X (k+1) ω)) ∂P =
              ∫ ω, Y ω ∂P + ∫ ω, l * (Y ω * X (k+1) ω) ∂P :=
            integral_add hYint (hYX.const_mul l)
          rw [e1, e2, integral_const_mul, integral_const_mul]
      _ = ∫ ω, (Y ω + c * (Y ω * V (k+1) ω)) ∂P := by
          have e3 : ∫ ω, (Y ω + c * (Y ω * V (k+1) ω)) ∂P =
              ∫ ω, Y ω ∂P + ∫ ω, c * (Y ω * V (k+1) ω) ∂P :=
            integral_add hYint (hYV.const_mul c)
          rw [hYX0, hYX2V, e3, integral_const_mul]; ring
      _ ≤ ∫ ω, Real.exp (l * ∑ i ∈ Finset.Icc 1 k, X i ω
            - c * ∑ i ∈ Finset.Icc 1 k, V i ω) ∂P := by
          apply integral_mono_ae i3 ihint
          filter_upwards with ω
          show Y ω + c * (Y ω * V (k+1) ω) ≤ _
          have hY : Y ω = Real.exp (l * ∑ i ∈ Finset.Icc 1 k, X i ω
              - c * ∑ i ∈ Finset.Icc 1 k, V i ω - c * V (k+1) ω) := rfl
          have h1 := Real.add_one_le_exp (c * V (k+1) ω)
          have h2 : Y ω * Real.exp (c * V (k+1) ω) = Real.exp (l * ∑ i ∈ Finset.Icc 1 k, X i ω
              - c * ∑ i ∈ Finset.Icc 1 k, V i ω) := by
            rw [hY, ← Real.exp_add]; congr 1; ring
          have h3 := hYpos ω
          nlinarith
      _ ≤ 1 := ihle

theorem aux_fr_final {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (T : ℕ) (b : ℝ)
    (hmeas : ∀ i ∈ Finset.Icc 1 T, Measurable[𝓕 (i + 1)] (X i))
    (hint : ∀ i ∈ Finset.Icc 1 T, Integrable (X i) P)
    (hint_sq : ∀ i ∈ Finset.Icc 1 T, Integrable (fun ω => X i ω ^ 2) P)
    (hmds : ∀ i ∈ Finset.Icc 1 T, P[X i | 𝓕 i] =ᵐ[P] 0)
    (hb : ∀ i ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, X i ω ≤ b)
    (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    P.real {ω | a ≤ ∑ i ∈ Finset.Icc 1 T, X i ω ∧
        ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | 𝓕 i] ω ≤ v} ≤
      Real.exp (-a ^ 2 / (2 * v + 2 * a * b / 3)) := by
  by_cases hD : 2 * v + 2 * a * b / 3 ≤ 0
  · have h1 : 1 ≤ Real.exp (-a ^ 2 / (2 * v + 2 * a * b / 3)) := by
      apply Real.one_le_exp
      exact div_nonneg_of_nonpos (by nlinarith) hD
    exact le_trans measureReal_le_one h1
  push Not at hD
  have hD' : 0 < v + a * b / 3 := by linarith
  set l := a / (v + a * b / 3) with hl_def
  have hl : 0 < l := div_pos ha hD'
  have hne' : v * 3 + a * b ≠ 0 := by
    have : 0 < v * 3 + a * b := by linarith
    exact this.ne'
  have hd : 1 - l * b / 3 = v / (v + a * b / 3) := by
    have hne : v + a * b / 3 ≠ 0 := hD'.ne'
    rw [hl_def]
    field_simp
    ring
  have hdpos : 0 < 1 - l * b / 3 := by rw [hd]; exact div_pos hv hD'
  set c := l ^ 2 / (2 * (1 - l * b / 3)) with hc_def
  have hc : 0 ≤ c := by positivity
  have hpw : ∀ x ≤ b, Real.exp (l * x) ≤ 1 + l * x + c * x ^ 2 := fun x hx =>
    aux_fr_pw l b x hl hdpos hx
  obtain ⟨hMint, hMle⟩ := aux_fr_main P 𝓕 X T b hmeas hint hint_sq hmds hb l c hl hc hpw
    (fun i => P[fun ω' => X i ω' ^ 2 | 𝓕 i]) (fun i => rfl) T le_rfl
  set ε := Real.exp (l * a - c * v) with hε
  have hεpos : 0 < ε := Real.exp_pos _
  have hsub : {ω | a ≤ ∑ i ∈ Finset.Icc 1 T, X i ω ∧
        ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | 𝓕 i] ω ≤ v} ⊆
      {ω | ε ≤ Real.exp (l * ∑ i ∈ Finset.Icc 1 T, X i ω
        - c * ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | 𝓕 i] ω)} := by
    intro ω hω
    obtain ⟨h1, h2⟩ := hω
    simp only [Set.mem_ofPred_eq, hε]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left h1 hl.le, mul_le_mul_of_nonneg_left h2 hc]
  have hmk := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le)) hMint ε
  have hmono := measureReal_mono (μ := P) hsub
  have key : P.real {ω | ε ≤ Real.exp (l * ∑ i ∈ Finset.Icc 1 T, X i ω
        - c * ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | 𝓕 i] ω)} ≤ ε⁻¹ := by
    have h1 := hmk.trans hMle
    calc _ = ε⁻¹ * (ε * P.real {ω | ε ≤ Real.exp (l * ∑ i ∈ Finset.Icc 1 T, X i ω
        - c * ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | 𝓕 i] ω)}) := by
          rw [← mul_assoc, inv_mul_cancel₀ hεpos.ne', one_mul]
      _ ≤ ε⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hεpos.le)
      _ = ε⁻¹ := mul_one _
  have halg : ε⁻¹ = Real.exp (-a ^ 2 / (2 * v + 2 * a * b / 3)) := by
    rw [hε, ← Real.exp_neg]
    congr 1
    rw [hc_def, hd, hl_def]
    field_simp
    ring
  linarith


end StochLinOpt.UpperBound

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
namespace StochLinOpt.UpperBound

lemma cb_fixed_tail {n : ℕ} (hn : 0 < n) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℕ mΩ)
    (D : Set (Fin n → ℝ)) (hD_cube : ∀ y ∈ D, ∀ i, |y i| ≤ 1)
    (μ : Fin n → ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (x : ℕ → Ω → Fin n → ℝ) (ℓ : ℕ → Ω → ℝ)
    (hx : ∀ t, 1 ≤ t → Measurable[𝓕 t] (x t))
    (hℓ : ∀ t, 1 ≤ t → Measurable[𝓕 (t+1)] (ℓ t))
    (hℓb : ∀ t, 1 ≤ t → ∀ ω, |ℓ t ω| ≤ 1)
    (hηb : ∀ t, 1 ≤ t → ∀ ω, |ℓ t ω - μ ⬝ᵥ x t ω| ≤ 1)
    (hmean : ∀ t, 1 ≤ t → P[ℓ t | 𝓕 t] =ᵐ[P] fun ω => μ ⬝ᵥ x t ω)
    (hrun : ∀ ω, IsConfidenceBall2Run D δ (fun t => x t ω) (fun t => ℓ t ω))
    (t : ℕ) (ht : 2 ≤ t) :
    P.real {ω | beta n δ t/2 < ∑ s ∈ Finset.Ico 1 t,
      mIncrement δ μ (fun r => x r ω) (fun r => ℓ r ω) s} ≤ δ/(t : ℝ)^2 := by
  let M : ℕ → Ω → ℝ := fun s ω => mIncrement δ μ (fun r => x r ω) (fun r => ℓ r ω) s
  let C : ℕ → Ω → ℝ := fun s ω => cbCoeff δ μ (fun r => x r ω) (fun r => ℓ r ω) s
  have hp := cb_increment_properties P 𝓕 δ μ x ℓ hx hℓ hℓb hηb hmean
  have he : Finset.Ico 1 t = Finset.Icc 1 (t-1) := by ext s;simp;omega
  have hs : ∀ s ∈ Finset.Icc 1 (t-1), 1 ≤ s := fun s hs => (Finset.mem_Icc.mp hs).1
  have hb : ∀ s ∈ Finset.Icc 1 (t-1), ∀ᵐ ω ∂P, M s ω ≤ Real.sqrt (beta n δ t) := by
    intro s hst
    refine Filter.Eventually.of_forall fun ω => ?_
    have h1 := (hp s (hs s hst)).2.2.2.2.2 ω
    have hstt : s ≤ t := by have hst' := (Finset.mem_Icc.mp hst).2;omega
    have hB := aux_ssq_beta_mono (n := n) hδ hδ1 (hs s hst) hstt
    exact (le_abs_self _).trans (h1.trans (Real.sqrt_le_sqrt hB))
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ht' : (1 : ℝ) < t := by exact_mod_cast ht
  have hB := cb_beta_positive (n := n) hδ hδ1 (by omega : 1 ≤ t)
  have hv : 0 < 4*beta n δ t*n*Real.log t := by have := Real.log_pos ht';positivity
  have hfr := aux_fr_final P 𝓕 M (t-1) (Real.sqrt (beta n δ t))
    (fun s hst => (hp s (hs s hst)).1)
    (fun s hst => (hp s (hs s hst)).2.1)
    (fun s hst => (hp s (hs s hst)).2.2.1)
    (fun s hst => (hp s (hs s hst)).2.2.2.1) hb
    (beta n δ t/2) (4*beta n δ t*n*Real.log t) (by positivity) hv
  have hvar : ∀ᵐ ω ∂P, ∑ s ∈ Finset.Icc 1 (t-1), P[fun ω' => M s ω'^2 | 𝓕 s] ω
      ≤ 4*beta n δ t*n*Real.log t := by
    have hall : ∀ s ∈ Finset.Icc 1 (t-1), ∀ᵐ ω ∂P,
        P[fun ω' => M s ω'^2 | 𝓕 s] ω ≤ C s ω^2 :=
      fun s hst => (hp s (hs s hst)).2.2.2.2.1
    have hforall : ∀ᵐ ω ∂P, ∀ s ∈ Finset.Icc 1 (t-1),
        P[fun ω' => M s ω'^2 | 𝓕 s] ω ≤ C s ω^2 := by
      exact (ae_all_iff.2 (fun s => ae_all_iff.2 (hall s)))
    filter_upwards [hforall] with ω hω
    have hsum := cb_coeff_sum_bound hδ hδ1 μ (fun s => x s ω)
      (fun s => ℓ s ω) t (by omega) (fun s hst i => hD_cube _ (hrun ω s (Finset.mem_Ico.mp hst).1).1 i)
    exact (Finset.sum_le_sum (fun s hst => hω s hst)).trans (by simpa only [←he,C] using hsum)
  have hm : P.real {ω | beta n δ t/2 < ∑ s ∈ Finset.Ico 1 t,M s ω} ≤
      P.real {ω | beta n δ t/2 ≤ ∑ s ∈ Finset.Icc 1 (t-1),M s ω ∧
        ∑ s ∈ Finset.Icc 1 (t-1), P[fun ω' => M s ω'^2 | 𝓕 s] ω ≤ 4*beta n δ t*n*Real.log t} := by
    apply ENNReal.toReal_mono (measure_ne_top P _)
    apply measure_mono_ae
    filter_upwards [hvar] with ω hω
    intro h
    exact ⟨by simpa only [he] using h.le,hω⟩
  exact hm.trans (hfr.trans (cb_freedman_numeric hn hδ hδ1 ht))

lemma cb_tail_partial {δ : ℝ} (hδ : 0 ≤ δ) (N : ℕ) :
    ∑ k ∈ Finset.range N, δ/((k : ℝ)+2)^2 ≤ δ-δ/((N : ℝ)+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h : δ/((N : ℝ)+2)^2 ≤ δ/((N : ℝ)+1)-δ/((N : ℝ)+2) := by
      have h1 : 0 < (N : ℝ)+1 := by positivity
      have h2 : 0 < (N : ℝ)+2 := by positivity
      rw [le_sub_iff_add_le]
      field_simp
      nlinarith [mul_nonneg hδ (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    push_cast
    have hadd : (N : ℝ)+1+1 = (N : ℝ)+2 := by ring
    rw [hadd]
    linarith

lemma cb_tail_tsum {δ : ℝ} (hδ : 0 ≤ δ) :
    ∑' k : ℕ, ENNReal.ofReal (δ/((k : ℝ)+2)^2) ≤ ENNReal.ofReal δ := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro N
  rw [←ENNReal.ofReal_sum_of_nonneg (fun k _ => div_nonneg hδ (sq_nonneg _))]
  apply ENNReal.ofReal_le_ofReal
  exact (cb_tail_partial hδ N).trans (sub_le_self _ (by positivity))

end StochLinOpt.UpperBound

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
namespace StochLinOpt.UpperBound

lemma cb_martingale_checked {n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℕ mΩ)
    (D : Set (Fin n → ℝ)) (hD_compact : IsCompact D)
    (hD_basis : ∀ i : Fin n, (Pi.single i (1 : ℝ) : Fin n → ℝ) ∈ D)
    (hD_cube : ∀ y ∈ D, ∀ i, |y i| ≤ 1)
    (μ : Fin n → ℝ) (hμD : ∀ y ∈ D, |μ ⬝ᵥ y| ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (x : ℕ → Ω → Fin n → ℝ) (ℓ : ℕ → Ω → ℝ)
    (hx_meas : ∀ t : ℕ, 1 ≤ t → Measurable[𝓕 t] (x t))
    (hℓ_meas : ∀ t : ℕ, 1 ≤ t → Measurable[𝓕 (t + 1)] (ℓ t))
    (hℓ_bdd : ∀ t : ℕ, 1 ≤ t → ∀ ω, |ℓ t ω| ≤ 1)
    (hη_bdd : ∀ t : ℕ, 1 ≤ t → ∀ ω, |ℓ t ω - μ ⬝ᵥ x t ω| ≤ 1)
    (hmean : ∀ t : ℕ, 1 ≤ t → P[ℓ t | 𝓕 t] =ᵐ[P] fun ω => μ ⬝ᵥ x t ω)
    (hrun : ∀ ω, IsConfidenceBall2Run D δ (fun t => x t ω) (fun t => ℓ t ω)) :
    1 - δ ≤ P.real {ω | ∀ t : ℕ, 1 ≤ t →
      ∑ τ ∈ Finset.Ico 1 t, mIncrement δ μ (fun s => x s ω) (fun s => ℓ s ω) τ ≤
        beta n δ t / 2} := by
  classical
  by_cases hn : 0 < n
  · let G : Set Ω := {ω | ∀ t : ℕ,1 ≤ t →
      ∑ s ∈ Finset.Ico 1 t,mIncrement δ μ (fun r => x r ω) (fun r => ℓ r ω) s ≤ beta n δ t/2}
    let B : ℕ → Set Ω := fun k => {ω | beta n δ (k+2)/2 <
      ∑ s ∈ Finset.Ico 1 (k+2),mIncrement δ μ (fun r => x r ω) (fun r => ℓ r ω) s}
    have hp := cb_increment_properties P 𝓕 δ μ x ℓ hx_meas hℓ_meas hℓ_bdd hη_bdd hmean
    have hG : MeasurableSet G := by
      have he : G = ⋂ t : ℕ,{ω | 1 ≤ t →
          ∑ s ∈ Finset.Ico 1 t,mIncrement δ μ (fun r => x r ω) (fun r => ℓ r ω) s ≤ beta n δ t/2} := by
        ext ω;simp [G]
      rw [he]
      apply MeasurableSet.iInter
      intro t
      by_cases ht : 1 ≤ t
      · have hm : Measurable (fun ω => ∑ s ∈ Finset.Ico 1 t,
            mIncrement δ μ (fun r => x r ω) (fun r => ℓ r ω) s) :=
          Finset.measurable_sum _ fun s hs => ((hp s (Finset.mem_Ico.mp hs).1).1).mono (𝓕.le _) le_rfl
        simpa only [ht,true_implies] using measurableSet_le hm (measurable_const (a := beta n δ t/2))
      · simp [ht]
    have hsub : Gᶜ ⊆ ⋃ k,B k := by
      intro ω hω
      change ¬(∀ t : ℕ,1 ≤ t →
        ∑ s ∈ Finset.Ico 1 t,mIncrement δ μ (fun r => x r ω) (fun r => ℓ r ω) s ≤ beta n δ t/2) at hω
      push Not at hω
      obtain ⟨t,ht,hbad⟩ := hω
      have ht2 : 2 ≤ t := by
        by_contra h
        have ht1 : t = 1 := by omega
        subst t
        simp only [Finset.Ico_self,Finset.sum_empty] at hbad
        have hB := cb_beta_nonneg (n := n) δ 1
        linarith
      refine Set.mem_iUnion.mpr ⟨t-2,?_⟩
      change beta n δ (t-2+2)/2 < _
      simpa only [Nat.sub_add_cancel ht2] using hbad
    have hB : ∀ k, P (B k) ≤ ENNReal.ofReal (δ/((k : ℝ)+2)^2) := by
      intro k
      have h := cb_fixed_tail hn P 𝓕 D hD_cube μ hδ hδ1 x ℓ hx_meas hℓ_meas hℓ_bdd hη_bdd hmean hrun (k+2) (by omega)
      rw [←ENNReal.ofReal_toReal (measure_ne_top P (B k))]
      apply ENNReal.ofReal_le_ofReal
      simpa only [B,Nat.cast_add,Nat.cast_ofNat,measureReal_def] using h
    have hfail : P Gᶜ ≤ ENNReal.ofReal δ :=
      (measure_mono hsub).trans ((measure_iUnion_le B).trans
        ((ENNReal.tsum_le_tsum hB).trans (cb_tail_tsum hδ.le)))
    have hfailR : P.real Gᶜ ≤ δ := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfail
      simpa only [ENNReal.toReal_ofReal hδ.le,measureReal_def] using h
    have hprob := measureReal_add_measureReal_compl (μ := P) hG
    rw [probReal_univ] at hprob
    change 1-δ ≤ P.real G
    linarith
  · have hn0 : n = 0 := by omega
    subst n
    have hG : {ω | ∀ t : ℕ,1 ≤ t →
        ∑ s ∈ Finset.Ico 1 t,mIncrement δ μ (fun r => x r ω) (fun r => ℓ r ω) s ≤ beta 0 δ t/2} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq,Set.mem_univ,iff_true]
      intro t ht
      have hM : ∀ s,mIncrement δ μ (fun r => x r ω) (fun r => ℓ r ω) s = 0 := by
        intro s
        simp [mIncrement,dotProduct]
      simpa only [hM,Finset.sum_const_zero] using
        (div_nonneg (cb_beta_nonneg (n := 0) δ t) (by norm_num : (0 : ℝ) ≤ 2))
    rw [hG,probReal_univ]
    linarith

end StochLinOpt.UpperBound

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix
namespace StochLinOpt.UpperBound

lemma cb_noise_drift {n : ℕ} (μ : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    (t : ℕ) (ht : 1 ≤ t)
    (hx : ∀ s ∈ Finset.Ico 1 t, ∀ i, |x s i| ≤ 1)
    (hη : ∀ s ∈ Finset.Ico 1 t, |ℓ s - μ ⬝ᵥ x s| ≤ 1) :
    ∑ s ∈ Finset.Ico 1 t,(ℓ s-μ ⬝ᵥ x s)^2*width x s^2/(1+width x s^2)
      ≤ n*Real.log t := by
  apply le_trans _ (cb_logsum_bound x t ht hx)
  apply Finset.sum_le_sum
  intro s hs
  have hnoise : (ℓ s-μ ⬝ᵥ x s)^2 ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) (hη s hs) 2
    simpa only [sq_abs,one_pow] using h
  have hp : 0 < 1+width x s^2 := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos hp
  have he : 1-(1+width x s^2)⁻¹ = width x s^2/(1+width x s^2) := by field_simp;ring
  rw [he] at hlog
  apply le_trans _ hlog
  apply div_le_div_of_nonneg_right _ hp.le
  simpa using mul_le_mul_of_nonneg_right hnoise (sq_nonneg (width x s))

lemma cb_confidence_path {n : ℕ} (D : Set (Fin n → ℝ)) (μ : Fin n → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    (hD_basis : ∀ i : Fin n, (Pi.single i (1 : ℝ) : Fin n → ℝ) ∈ D)
    (hμD : ∀ y ∈ D, |μ ⬝ᵥ y| ≤ 1)
    (hx : ∀ t,1 ≤ t → ∀ i, |x t i| ≤ 1)
    (hη : ∀ t,1 ≤ t → |ℓ t-μ ⬝ᵥ x t| ≤ 1)
    (hbase : (n : ℝ) ≤ beta n δ 1)
    (hmart : ∀ t,1 ≤ t → ∑ s ∈ Finset.Ico 1 t,mIncrement δ μ x ℓ s ≤ beta n δ t/2) :
    ∀ t,1 ≤ t → zStat μ x ℓ t ≤ beta n δ t := by
  classical
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro ht
    by_cases ht1 : t = 1
    · subst t
      rw [cb_z_initial μ x ℓ le_rfl]
      exact (cb_mu_norm D μ hD_basis hμD).trans hbase
    · have ht2 : 2 ≤ t := by omega
      have hescape : ∀ s ∈ Finset.Ico 1 t,escapeInd δ μ x ℓ s = 1 := by
        intro s hs
        unfold escapeInd
        apply if_pos
        intro r hr
        exact ih r (lt_of_le_of_lt (Finset.mem_Icc.mp hr).2 (Finset.mem_Ico.mp hs).2) (Finset.mem_Icc.mp hr).1
      have heq : 2*∑ s ∈ Finset.Ico 1 t,
          (ℓ s-μ ⬝ᵥ x s)*(x s ⬝ᵥ (muHat x ℓ s-μ))/(1+width x s^2) =
          ∑ s ∈ Finset.Ico 1 t,mIncrement δ μ x ℓ s := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        unfold mIncrement
        rw [hescape s hs]
        ring
      have hz := cb_zStat_checked D μ x ℓ hD_basis hμD t
      rw [heq] at hz
      have hnoise := cb_noise_drift μ x ℓ t ht
        (fun s hs => hx s (Finset.mem_Ico.mp hs).1)
        (fun s hs => hη s (Finset.mem_Ico.mp hs).1)
      have hM := hmart t ht
      have hB := cb_beta_drift (n := n) hδ hδ1 ht2
      linarith

lemma cb_ball_iff {n : ℕ} (δ : ℝ) (μ : Fin n → ℝ) (x : ℕ → Fin n → ℝ)
    (ℓ : ℕ → ℝ) (t : ℕ) : μ ∈ confBall δ x ℓ t ↔ zStat μ x ℓ t ≤ beta n δ t := by
  change (μ-muHat x ℓ t) ⬝ᵥ (designMatrix x t *ᵥ (μ-muHat x ℓ t)) ≤ beta n δ t ↔ _
  have he : μ-muHat x ℓ t = -(muHat x ℓ t-μ) := by abel
  rw [he,mulVec_neg,neg_dotProduct,dotProduct_neg,neg_neg]
  rfl

lemma cb_confidence_checked {n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℕ mΩ)
    (D : Set (Fin n → ℝ)) (hD_compact : IsCompact D)
    (hD_basis : ∀ i : Fin n, (Pi.single i (1 : ℝ) : Fin n → ℝ) ∈ D)
    (hD_cube : ∀ y ∈ D, ∀ i, |y i| ≤ 1)
    (μ : Fin n → ℝ) (hμD : ∀ y ∈ D, |μ ⬝ᵥ y| ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (x : ℕ → Ω → Fin n → ℝ) (ℓ : ℕ → Ω → ℝ)
    (hx_meas : ∀ t : ℕ, 1 ≤ t → Measurable[𝓕 t] (x t))
    (hℓ_meas : ∀ t : ℕ, 1 ≤ t → Measurable[𝓕 (t+1)] (ℓ t))
    (hℓ_bdd : ∀ t : ℕ, 1 ≤ t → ∀ ω, |ℓ t ω| ≤ 1)
    (hη_bdd : ∀ t : ℕ, 1 ≤ t → ∀ ω, |ℓ t ω-μ ⬝ᵥ x t ω| ≤ 1)
    (hmean : ∀ t : ℕ, 1 ≤ t → P[ℓ t | 𝓕 t] =ᵐ[P] fun ω => μ ⬝ᵥ x t ω)
    (hrun : ∀ ω, IsConfidenceBall2Run D δ (fun t => x t ω) (fun t => ℓ t ω))
    (hβ₁ : (n : ℝ) ≤ (8/3*Real.log (1/δ))^2) :
    1-δ ≤ P.real {ω | ∀ t : ℕ,1 ≤ t →
      μ ∈ confBall δ (fun s => x s ω) (fun s => ℓ s ω) t} := by
  have hbase : (n : ℝ) ≤ beta n δ 1 := by
    apply hβ₁.trans
    unfold beta
    simpa using le_max_right (0 : ℝ) ((8/3*Real.log (1/δ))^2)
  have hm := cb_martingale_checked P 𝓕 D hD_compact hD_basis hD_cube μ hμD δ hδ hδ1 x ℓ hx_meas hℓ_meas hℓ_bdd hη_bdd hmean hrun
  apply hm.trans
  apply measureReal_mono (h₂ := measure_ne_top P _)
  intro ω hω t ht
  rw [cb_ball_iff]
  exact cb_confidence_path D μ δ hδ hδ1 (fun s => x s ω) (fun s => ℓ s ω) hD_basis hμD
    (fun s hs => hD_cube _ (hrun ω s hs).1) (fun s hs => hη_bdd s hs ω) hbase hω t ht

end StochLinOpt.UpperBound

/- Regret square bound credited to mrfancypants, accepted submission d48d5e68-5536-4955-b058-d3975985f0f8. -/


open StochLinOpt.UpperBound
open Matrix

theorem cb_sum_sq_checked {n : ℕ} (D : Set (Fin n → ℝ)) (δ : ℝ)
    (μ xstar : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    (hD_cube : ∀ y ∈ D, ∀ i, |y i| ≤ 1)
    (hμD : ∀ y ∈ D, |μ ⬝ᵥ y| ≤ 1)
    (hxstar : xstar ∈ D ∧ ∀ y ∈ D, μ ⬝ᵥ xstar ≤ μ ⬝ᵥ y)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hβ₁ : 1 ≤ beta n δ 1)
    (hrun : IsConfidenceBall2Run D δ x ℓ) (T : ℕ)
    (hμ : ∀ t ∈ Finset.Icc 1 T, μ ∈ confBall δ x ℓ t) :
    ∑ t ∈ Finset.Icc 1 T, (μ ⬝ᵥ x t - μ ⬝ᵥ xstar) ^ 2 ≤
      8 * n * beta n δ T * Real.log (T + 1) := by
  have hround : ∀ t ∈ Finset.Icc 1 T, (μ ⬝ᵥ x t - μ ⬝ᵥ xstar) ^ 2 ≤
      8 * beta n δ T * Real.log (1 + width x t ^ 2) := by
    intro t ht
    obtain ⟨ht1, htT⟩ := Finset.mem_Icc.mp ht
    obtain ⟨hxD, μt, hμt, hmin⟩ := hrun t ht1
    have hApd := aux_ssq_posDef x t
    have hw2 := aux_ssq_width_sq x t
    have hw0 : 0 ≤ width x t ^ 2 := sq_nonneg _
    have hr0 : 0 ≤ μ ⬝ᵥ x t - μ ⬝ᵥ xstar := by linarith [hxstar.2 _ hxD]
    have hr2 : μ ⬝ᵥ x t - μ ⬝ᵥ xstar ≤ 2 := by
      have h1 := hμD _ hxD
      have h2 := hμD _ hxstar.1
      rw [abs_le] at h1 h2
      linarith
    have hle : μ ⬝ᵥ x t - μ ⬝ᵥ xstar ≤ (μ - μt) ⬝ᵥ x t := by
      have := hmin μ (hμ t ht) xstar hxstar.1
      rw [sub_dotProduct]; linarith
    have hball : (μ - μt) ⬝ᵥ (designMatrix x t *ᵥ (μ - μt)) ≤ 4 * beta n δ t := by
      have h := aux_ssq_par (designMatrix x t) hApd.posSemidef (μ - muHat x ℓ t)
        (μt - muHat x ℓ t)
      have e : (μ - muHat x ℓ t) - (μt - muHat x ℓ t) = μ - μt := by abel
      rw [e] at h
      have h1 : (μ - muHat x ℓ t) ⬝ᵥ (designMatrix x t *ᵥ (μ - muHat x ℓ t)) ≤ beta n δ t :=
        hμ t ht
      have h2 : (μt - muHat x ℓ t) ⬝ᵥ (designMatrix x t *ᵥ (μt - muHat x ℓ t)) ≤ beta n δ t :=
        hμt
      linarith
    have hcs := aux_ssq_cs (designMatrix x t) hApd (μ - μt) (x t)
    have hsq : (μ ⬝ᵥ x t - μ ⬝ᵥ xstar) ^ 2 ≤ 4 * beta n δ t * width x t ^ 2 := by
      calc (μ ⬝ᵥ x t - μ ⬝ᵥ xstar) ^ 2 ≤ ((μ - μt) ⬝ᵥ x t) ^ 2 := pow_le_pow_left₀ hr0 hle 2
        _ ≤ _ := hcs
        _ ≤ 4 * beta n δ t * width x t ^ 2 := by
          rw [hw2]
          exact mul_le_mul_of_nonneg_right hball (aux_ssq_quad_nonneg x t)
    have hβt1 : 1 ≤ beta n δ t := le_trans hβ₁ (aux_ssq_beta_mono hδ hδ1 le_rfl ht1)
    have hmin' : (μ ⬝ᵥ x t - μ ⬝ᵥ xstar) ^ 2 ≤ 4 * beta n δ t * min (width x t ^ 2) 1 := by
      rcases le_total (width x t ^ 2) 1 with h | h
      · rw [min_eq_left h]; exact hsq
      · rw [min_eq_right h]; nlinarith
    have hlog := aux_ssq_min_log hw0
    have hlog0 : 0 ≤ Real.log (1 + width x t ^ 2) := Real.log_nonneg (by linarith)
    have hβT : beta n δ t ≤ beta n δ T := aux_ssq_beta_mono hδ hδ1 ht1 htT
    calc (μ ⬝ᵥ x t - μ ⬝ᵥ xstar) ^ 2 ≤ 4 * beta n δ t * min (width x t ^ 2) 1 := hmin'
      _ ≤ 4 * beta n δ t * (2 * Real.log (1 + width x t ^ 2)) := by
          apply mul_le_mul_of_nonneg_left hlog; linarith
      _ = 8 * beta n δ t * Real.log (1 + width x t ^ 2) := by ring
      _ ≤ 8 * beta n δ T * Real.log (1 + width x t ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ hlog0; linarith
  have hβT0 : 0 ≤ beta n δ T := by
    unfold StochLinOpt.UpperBound.beta; exact le_max_of_le_right (sq_nonneg _)
  have hx : ∀ t ∈ Finset.Icc 1 T, ∀ i, |x t i| ≤ 1 := by
    intro t ht i
    exact hD_cube _ (hrun t (Finset.mem_Icc.mp ht).1).1 i
  calc ∑ t ∈ Finset.Icc 1 T, (μ ⬝ᵥ x t - μ ⬝ᵥ xstar) ^ 2
      ≤ ∑ t ∈ Finset.Icc 1 T, 8 * beta n δ T * Real.log (1 + width x t ^ 2) :=
        Finset.sum_le_sum hround
    _ = 8 * beta n δ T * Real.log (designMatrix x (T+1)).det := by
        rw [← Finset.mul_sum, aux_ssq_sum_log]
    _ ≤ 8 * beta n δ T * (n * Real.log ((T:ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left (aux_ssq_logdet_le x T hx); linarith
    _ = 8 * n * beta n δ T * Real.log (T + 1) := by ring

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix
namespace StochLinOpt.UpperBound

lemma cb_regret_path {n : ℕ} (D : Set (Fin n → ℝ)) (δ : ℝ)
    (μ xstar : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    (hD_cube : ∀ y ∈ D,∀ i,|y i| ≤ 1) (hμD : ∀ y ∈ D,|μ ⬝ᵥ y| ≤ 1)
    (hxstar : xstar ∈ D ∧ ∀ y ∈ D,μ ⬝ᵥ xstar ≤ μ ⬝ᵥ y)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hbase : (n : ℝ) ≤ beta n δ 1)
    (hrun : IsConfidenceBall2Run D δ x ℓ)
    (hμ : ∀ t,1 ≤ t → μ ∈ confBall δ x ℓ t) (T : ℕ) (hT : 1 ≤ T) :
    regret μ xstar x T ≤ Real.sqrt (8*n*T*beta n δ T*Real.log (T+1)) := by
  by_cases hn : 0 < n
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hs := cb_sum_sq_checked D δ μ xstar x ℓ hD_cube hμD hxstar hδ hδ1
      (hn1.trans hbase) hrun T (fun t ht => hμ t (Finset.mem_Icc.mp ht).1)
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.Icc 1 T)
      (f := fun t => μ ⬝ᵥ x t-μ ⬝ᵥ xstar)
    have hcard : (Finset.Icc 1 T).card = T := by simp
    rw [hcard] at hcs
    have hR : regret μ xstar x T^2 ≤ 8*n*T*beta n δ T*Real.log (T+1) := by
      have h := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg T : (0 : ℝ) ≤ T)
      dsimp [regret]
      nlinarith
    have hB := cb_beta_nonneg (n := n) δ T
    have hlog : 0 ≤ Real.log (T+1) := Real.log_nonneg (by have h0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T;linarith)
    have hp : 0 ≤ 8*(n : ℝ)*T*beta n δ T*Real.log (T+1) := by positivity
    have hsq := Real.sq_sqrt hp
    have hpos := Real.sqrt_nonneg (8*(n : ℝ)*T*beta n δ T*Real.log (T+1))
    nlinarith
  · have hn0 : n = 0 := by omega
    subst n
    simp [regret,dotProduct]

lemma cb_root_checked {n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℕ mΩ)
    (D : Set (Fin n → ℝ)) (hD_compact : IsCompact D)
    (hD_basis : ∀ i : Fin n,(Pi.single i (1 : ℝ) : Fin n → ℝ) ∈ D)
    (hD_cube : ∀ y ∈ D,∀ i,|y i| ≤ 1)
    (μ : Fin n → ℝ) (hμD : ∀ y ∈ D,|μ ⬝ᵥ y| ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (x : ℕ → Ω → Fin n → ℝ) (ℓ : ℕ → Ω → ℝ)
    (hx_meas : ∀ t : ℕ,1 ≤ t → Measurable[𝓕 t] (x t))
    (hℓ_meas : ∀ t : ℕ,1 ≤ t → Measurable[𝓕 (t+1)] (ℓ t))
    (hℓ_bdd : ∀ t : ℕ,1 ≤ t → ∀ ω,|ℓ t ω| ≤ 1)
    (hη_bdd : ∀ t : ℕ,1 ≤ t → ∀ ω,|ℓ t ω-μ ⬝ᵥ x t ω| ≤ 1)
    (hmean : ∀ t : ℕ,1 ≤ t → P[ℓ t | 𝓕 t] =ᵐ[P] fun ω => μ ⬝ᵥ x t ω)
    (hrun : ∀ ω,IsConfidenceBall2Run D δ (fun t => x t ω) (fun t => ℓ t ω))
    (hβ₁ : (n : ℝ) ≤ (8/3*Real.log (1/δ))^2)
    (xstar : Fin n → ℝ) (hxstar : xstar ∈ D ∧ ∀ y ∈ D,μ ⬝ᵥ xstar ≤ μ ⬝ᵥ y) :
    1-δ ≤ P.real {ω | ∀ T : ℕ,1 ≤ T →
      regret μ xstar (fun t => x t ω) T ≤ Real.sqrt (8*n*T*beta n δ T*Real.log (T+1))} := by
  have hc := cb_confidence_checked P 𝓕 D hD_compact hD_basis hD_cube μ hμD δ hδ hδ1 x ℓ
    hx_meas hℓ_meas hℓ_bdd hη_bdd hmean hrun hβ₁
  have hbase : (n : ℝ) ≤ beta n δ 1 := by
    apply hβ₁.trans
    unfold beta
    simpa using le_max_right (0 : ℝ) ((8/3*Real.log (1/δ))^2)
  apply hc.trans
  apply measureReal_mono (h₂ := measure_ne_top P _)
  intro ω hω T hT
  exact cb_regret_path D δ μ xstar (fun t => x t ω) (fun t => ℓ t ω)
    hD_cube hμD hxstar hδ hδ1 hbase (hrun ω) hω T hT

end StochLinOpt.UpperBound

open MeasureTheory ProbabilityTheory Matrix StochLinOpt.UpperBound
theorem solution {n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℕ mΩ)
    (D : Set (Fin n → ℝ)) (hD_compact : IsCompact D)
    (hD_basis : ∀ i : Fin n, (Pi.single i (1 : ℝ) : Fin n → ℝ) ∈ D)
    (hD_cube : ∀ y ∈ D, ∀ i, |y i| ≤ 1)
    (μ : Fin n → ℝ) (hμD : ∀ y ∈ D, |μ ⬝ᵥ y| ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (x : ℕ → Ω → Fin n → ℝ) (ℓ : ℕ → Ω → ℝ)
    (hx_meas : ∀ t : ℕ, 1 ≤ t → Measurable[𝓕 t] (x t))
    (hℓ_meas : ∀ t : ℕ, 1 ≤ t → Measurable[𝓕 (t + 1)] (ℓ t))
    (hℓ_bdd : ∀ t : ℕ, 1 ≤ t → ∀ ω, |ℓ t ω| ≤ 1)
    (hη_bdd : ∀ t : ℕ, 1 ≤ t → ∀ ω, |ℓ t ω - μ ⬝ᵥ x t ω| ≤ 1)
    (hmean : ∀ t : ℕ, 1 ≤ t → P[ℓ t | 𝓕 t] =ᵐ[P] fun ω => μ ⬝ᵥ x t ω)
    (hrun : ∀ ω, IsConfidenceBall2Run D δ (fun t => x t ω) (fun t => ℓ t ω))
    (hβ₁ : (n : ℝ) ≤ (8 / 3 * Real.log (1 / δ)) ^ 2)
    (xstar : Fin n → ℝ) (hxstar : xstar ∈ D ∧ ∀ y ∈ D, μ ⬝ᵥ xstar ≤ μ ⬝ᵥ y) :
    1 - δ ≤ P.real {ω | ∀ T : ℕ, 1 ≤ T →
      regret μ xstar (fun t => x t ω) T ≤
        Real.sqrt (8 * n * T * beta n δ T * Real.log (T + 1))} := by
  exact cb_root_checked P 𝓕 D hD_compact hD_basis hD_cube μ hμD δ hδ hδ1 x ℓ hx_meas hℓ_meas hℓ_bdd hη_bdd hmean hrun hβ₁ xstar hxstar

#print axioms solution
