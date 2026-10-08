-- Prove2me | solution 1 for StochLinOpt.UpperBound.zStat_le
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T16:33:52.567482+00:00
-- url     : https://prove2.me/submissions/6e412cc4-20e4-4d0b-9ef5-23afff36dc03

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

open MeasureTheory ProbabilityTheory Matrix StochLinOpt.UpperBound
theorem solution {n : ℕ} (D : Set (Fin n → ℝ)) (μ : Fin n → ℝ)
    (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    (hD_basis : ∀ i : Fin n, (Pi.single i (1 : ℝ) : Fin n → ℝ) ∈ D)
    (hμD : ∀ y ∈ D, |μ ⬝ᵥ y| ≤ 1) (t : ℕ) :
    zStat μ x ℓ t ≤ n
      + 2 * ∑ τ ∈ Finset.Ico 1 t,
          (ℓ τ - μ ⬝ᵥ x τ) * (x τ ⬝ᵥ (muHat x ℓ τ - μ)) / (1 + width x τ ^ 2)
      + ∑ τ ∈ Finset.Ico 1 t,
          (ℓ τ - μ ⬝ᵥ x τ) ^ 2 * width x τ ^ 2 / (1 + width x τ ^ 2) := by
  exact cb_zStat_checked D μ x ℓ hD_basis hμD t

#print axioms solution
