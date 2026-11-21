-- Prove2me | solution 1 for SQMeanEstimation.ringInf_estimate
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:27:24.032173+00:00
-- url     : https://prove2.me/submissions/181cfd01-a7bd-469a-960c-00cb6bdc560f

import Mathlib
import Definitions.Def_SQMeanEstimation_lqNorm
import Definitions.Def_SQMeanEstimation_NonadaptiveSQ
import Definitions.Def_SQMeanEstimation_ValidVSTATAnswers
import Definitions.Def_SQMeanEstimation_ringInf
import Definitions.Def_SQMeanEstimation_ringDepth

open MeasureTheory

namespace Aux_SQMeanEstimation_ringInf_estimate

open SQMeanEstimation

noncomputable def tau (d : ℕ) (q : ℝ) : ℝ := (2 : ℝ) ^ (-ringDepth d q - 1)

noncomputable def rr (d : ℕ) (q : ℝ) (i : Fin d) (w : Fin d → ℝ) : ℝ :=
  ringInf (ringDepth d q) w i

theorem tau_pos (d : ℕ) (q : ℝ) : 0 < tau d q := zpow_pos (by norm_num) _

theorem rr_eq (d : ℕ) (q : ℝ) (i : Fin d) (w : Fin d → ℝ) :
    rr d q i w = if |w i| ≤ tau d q then w i else 0 := rfl

theorem rr_abs (d : ℕ) (q : ℝ) (i : Fin d) (w : Fin d → ℝ) : |rr d q i w| ≤ tau d q := by
  rw [rr_eq]
  split_ifs with h
  · exact h
  · rw [abs_zero]
    exact (tau_pos d q).le

theorem rr_abs_le (d : ℕ) (q : ℝ) (i : Fin d) (w : Fin d → ℝ) : |rr d q i w| ≤ |w i| := by
  rw [rr_eq]
  split_ifs
  · exact le_rfl
  · rw [abs_zero]
    exact abs_nonneg _

theorem rr_meas (d : ℕ) (q : ℝ) (i : Fin d) : Measurable (rr d q i) := by
  have h : rr d q i = fun w => if |w i| ≤ tau d q then w i else 0 := by
    funext w
    exact rr_eq d q i w
  rw [h]
  exact Measurable.ite (measurableSet_le (measurable_pi_apply i).abs measurable_const)
    (measurable_pi_apply i) measurable_const

theorem rr_int (d : ℕ) (q : ℝ) (i : Fin d) (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] :
    Integrable (rr d q i) μ :=
  Integrable.of_bound (rr_meas d q i).aestronglyMeasurable (tau d q)
    (Filter.Eventually.of_forall (fun w => by rw [Real.norm_eq_abs]; exact rr_abs d q i w))

theorem int_coord (d : ℕ) (q : ℝ) (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (i : Fin d) :
    (∫ w, ringInf (ringDepth d q) w ∂μ) i = ∫ w, rr d q i w ∂μ :=
  eval_integral (f := fun w => ringInf (ringDepth d q) w) (fun j => rr_int d q j μ) i

theorem p1a (d : ℕ) (q : ℝ) :
    (2 : ℝ) ^ (-ringDepth d q - 1) ≤ (2 : ℝ) ^ (1 - ⌊Real.logb 2 d / q⌋) := by
  apply le_of_eq
  unfold ringDepth
  congr 1
  ring

theorem p1b (d : ℕ) (hd : 1 ≤ d) (q : ℝ) (hq1 : 1 < q) :
    (2 : ℝ) ^ (1 - ⌊Real.logb 2 d / q⌋) ≤ 4 * (d : ℝ) ^ (-1 / q) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨L, hL⟩ : ∃ L, L = Real.logb 2 d / q := ⟨_, rfl⟩
  rw [← hL]
  have hF : L - 1 < (⌊L⌋ : ℝ) := Int.sub_one_lt_floor L
  have e1 : (2 : ℝ) ^ (1 - ⌊L⌋) = (2 : ℝ) ^ ((1 : ℝ) - ⌊L⌋) := by
    rw [← Real.rpow_intCast, Int.cast_sub, Int.cast_one]
  have h2L : (2 : ℝ) ^ L = (d : ℝ) ^ (1 / q) := by
    rw [hL, div_eq_mul_one_div, Real.rpow_mul (show (0 : ℝ) ≤ 2 by norm_num),
      Real.rpow_logb (b := 2) (by norm_num) (by norm_num) hdpos]
  have e2 : (2 : ℝ) ^ ((2 : ℝ) - L) = 4 * (d : ℝ) ^ (-1 / q) := by
    rw [Real.rpow_sub (show (0 : ℝ) < 2 by norm_num), h2L, Real.rpow_two, show (-1 / q) = -(1 / q) by ring,
      Real.rpow_neg hdpos.le, div_eq_mul_inv]
    norm_num
  calc (2 : ℝ) ^ (1 - ⌊L⌋) = (2 : ℝ) ^ ((1 : ℝ) - ⌊L⌋) := e1
    _ ≤ (2 : ℝ) ^ ((2 : ℝ) - L) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 4 * (d : ℝ) ^ (-1 / q) := e2

theorem tau_le (d : ℕ) (hd : 1 ≤ d) (q : ℝ) (hq1 : 1 < q) :
    tau d q ≤ 4 * (d : ℝ) ^ (-1 / q) :=
  le_trans (p1a d q) (p1b d hd q hq1)

theorem coord_err (d : ℕ) (q : ℝ) (ε' : ℝ) (hε : 0 < ε') (hε2 : ε' ≤ 2)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (i : Fin d) (vi : ℝ)
    (hτle : tau d q ≤ 4 * (d : ℝ) ^ (-1 / q))
    (hvi : |vi - ∫ w, (rr d q i w + tau d q) / (2 * tau d q) ∂μ| ≤
      vstatTol ((4 / ε') ^ 2) (∫ w, (rr d q i w + tau d q) / (2 * tau d q) ∂μ)) :
    |(2 * tau d q * vi - tau d q) - ∫ w, rr d q i w ∂μ| ≤ ε' * (d : ℝ) ^ (-1 / q) := by
  have hτp : 0 < tau d q := tau_pos d q
  have hpE : ∫ w, (rr d q i w + tau d q) / (2 * tau d q) ∂μ
      = (∫ w, rr d q i w ∂μ + tau d q) / (2 * tau d q) := by
    rw [integral_div, integral_add (rr_int d q i μ) (integrable_const (tau d q)), integral_const,
      probReal_univ, one_smul]
  rw [hpE] at hvi
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = tau d q := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = ∫ w, rr d q i w ∂μ := ⟨_, rfl⟩
  rw [← hτ, ← hE] at hvi ⊢
  rw [← hτ] at hτle hτp
  obtain ⟨p, hp⟩ : ∃ p, p = (E + τ) / (2 * τ) := ⟨_, rfl⟩
  rw [← hp] at hvi
  have htol : vstatTol ((4 / ε') ^ 2) p ≤ ε' / 8 := by
    unfold vstatTol
    apply max_le
    · rw [div_pow, one_div_div,
        div_le_div_iff₀ (show (0 : ℝ) < 4 ^ 2 by norm_num) (show (0 : ℝ) < 8 by norm_num)]
      nlinarith
    · have h1 : p * (1 - p) / (4 / ε') ^ 2 ≤ (ε' / 8) ^ 2 := by
        rw [div_le_iff₀ (show (0 : ℝ) < (4 / ε') ^ 2 by positivity)]
        have h14 : ε' / 8 * (4 / ε') = 1 / 2 := by
          have : ε' ≠ 0 := hε.ne'
          first
            | (field_simp; ring1)
            | field_simp
        have hq4 : (ε' / 8) ^ 2 * (4 / ε') ^ 2 = 1 / 4 := by
          rw [← mul_pow, h14]
          norm_num
        rw [hq4]
        nlinarith [sq_nonneg (p - 1 / 2)]
      calc Real.sqrt (p * (1 - p) / (4 / ε') ^ 2) ≤ Real.sqrt ((ε' / 8) ^ 2) :=
            Real.sqrt_le_sqrt h1
        _ = ε' / 8 := Real.sqrt_sq (by positivity)
  have hdiff : (2 * τ * vi - τ) - E = 2 * τ * (vi - p) := by
    have : τ ≠ 0 := hτp.ne'
    rw [hp]
    first
      | (field_simp; ring1)
      | field_simp
      | ring1
  rw [hdiff, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * τ)]
  calc 2 * τ * |vi - p| ≤ 2 * τ * (ε' / 8) :=
        mul_le_mul_of_nonneg_left (hvi.trans htol) (by positivity)
    _ = τ * (ε' / 4) := by ring
    _ ≤ 4 * (d : ℝ) ^ (-1 / q) * (ε' / 4) :=
        mul_le_mul_of_nonneg_right hτle (by positivity)
    _ = ε' * (d : ℝ) ^ (-1 / q) := by ring

theorem small_b (d : ℕ) (hd : 1 ≤ d) (q : ℝ) (hq1 : 1 < q) (ε' : ℝ) (hε : 0 < ε')
    (x : Fin d → ℝ) (hx : ∀ i, |x i| ≤ ε' * (d : ℝ) ^ (-1 / q)) : lqNorm q x ≤ ε' := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := hdpos.ne'
  have hq0 : q ≠ 0 := by linarith
  unfold lqNorm
  calc (∑ i, |x i| ^ q) ^ (1 / q)
      ≤ (∑ _i : Fin d, (ε' * (d : ℝ) ^ (-1 / q)) ^ q) ^ (1 / q) := by
        apply Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _))
        · exact Finset.sum_le_sum (fun i _ =>
            Real.rpow_le_rpow (abs_nonneg _) (hx i) (by linarith))
        · have : 0 < 1 / q := by positivity
          exact this.le
    _ = ε' := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.mul_rpow hε.le (Real.rpow_nonneg hdpos.le _), ← Real.rpow_mul hdpos.le,
          div_mul_cancel₀ _ hq0, Real.rpow_neg_one]
        rw [mul_left_comm, mul_inv_cancel₀ hd0, mul_one, ← Real.rpow_mul hε.le,
          mul_one_div_cancel hq0, Real.rpow_one]

theorem big_case (d : ℕ) (q : ℝ) (hq1 : 1 < q) (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ w ∂μ, lqNorm q w ≤ 1) (x : Fin d → ℝ)
    (hx : ∀ i, x i = (∫ w, ringInf (ringDepth d q) w ∂μ) i) : lqNorm q x ≤ 1 := by
  have hq0 : 0 ≤ q := by linarith
  have hJ : ∀ i, |x i| ^ q ≤ ∫ w, |rr d q i w| ^ q ∂μ := by
    intro i
    rw [hx i, int_coord]
    have hab : |∫ w, rr d q i w ∂μ| ≤ ∫ w, |rr d q i w| ∂μ := abs_integral_le_integral_abs
    have hgi : Integrable (fun w => |rr d q i w| ^ q) μ :=
      Integrable.of_bound ((rr_meas d q i).abs.pow_const q).aestronglyMeasurable
        (tau d q ^ q) (Filter.Eventually.of_forall (fun w => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
          exact Real.rpow_le_rpow (abs_nonneg _) (rr_abs d q i w) hq0))
    have hJen : (∫ w, |rr d q i w| ∂μ) ^ q ≤ ∫ w, |rr d q i w| ^ q ∂μ :=
      (convexOn_rpow hq1.le).map_integral_le (f := fun w => |rr d q i w|)
        (Real.continuous_rpow_const hq0).continuousOn isClosed_Ici
        (Filter.Eventually.of_forall (fun w => Set.mem_Ici.mpr (abs_nonneg _)))
        (rr_int d q i μ).abs hgi
    exact le_trans (Real.rpow_le_rpow (abs_nonneg _) hab hq0) hJen
  have hint : ∀ i, Integrable (fun w => |rr d q i w| ^ q) μ := by
    intro i
    exact Integrable.of_bound ((rr_meas d q i).abs.pow_const q).aestronglyMeasurable
        (tau d q ^ q) (Filter.Eventually.of_forall (fun w => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
          exact Real.rpow_le_rpow (abs_nonneg _) (rr_abs d q i w) hq0))
  have hpt : ∀ᵐ w ∂μ, ∑ i, |rr d q i w| ^ q ≤ 1 := by
    filter_upwards [hμ] with w hw
    have hT : ∑ i, |w i| ^ q ≤ 1 := by
      unfold lqNorm at hw
      by_contra h
      push_neg at h
      have := Real.one_lt_rpow h (by positivity : (0 : ℝ) < 1 / q)
      linarith
    calc ∑ i, |rr d q i w| ^ q ≤ ∑ i, |w i| ^ q :=
          Finset.sum_le_sum (fun i _ => Real.rpow_le_rpow (abs_nonneg _) (rr_abs_le d q i w) hq0)
      _ ≤ 1 := hT
  have hsumint : ∫ w, ∑ i, |rr d q i w| ^ q ∂μ ≤ 1 := by
    have := integral_mono_ae (integrable_finsetSum _ (fun i _ => hint i)) (integrable_const (1 : ℝ))
      hpt
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using this
  have hS : ∑ i, |x i| ^ q ≤ 1 := by
    calc ∑ i, |x i| ^ q ≤ ∑ i, ∫ w, |rr d q i w| ^ q ∂μ := Finset.sum_le_sum (fun i _ => hJ i)
      _ = ∫ w, ∑ i, |rr d q i w| ^ q ∂μ := (integral_finsetSum _ (fun i _ => hint i)).symm
      _ ≤ 1 := hsumint
  unfold lqNorm
  exact Real.rpow_le_one (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)) hS
    (by positivity)

end Aux_SQMeanEstimation_ringInf_estimate

open SQMeanEstimation Aux_SQMeanEstimation_ringInf_estimate in
theorem solution {d : ℕ} (hd : 1 ≤ d) (q : ℝ) (hq1 : 1 < q) (hq2 : q < 2) :
    ((2 : ℝ) ^ (-ringDepth d q - 1) ≤ (2 : ℝ) ^ (1 - ⌊Real.logb 2 d / q⌋) ∧
      (2 : ℝ) ^ (1 - ⌊Real.logb 2 d / q⌋) ≤ 4 * (d : ℝ) ^ (-1 / q)) ∧
    ∀ ε' : ℝ, 0 < ε' →
      ∃ A : NonadaptiveSQ d d,
        ∀ (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ], (∀ᵐ w ∂μ, lqNorm q w ≤ 1) →
          ∀ v : Fin d → ℝ, ValidVSTATAnswers μ ((4 / ε') ^ 2) A v →
            (ε' ≤ 2 → ∀ i, |A.output v i - (∫ w, ringInf (ringDepth d q) w ∂μ) i| ≤
                ε' * (d : ℝ) ^ (-1 / q)) ∧
            lqNorm q ((∫ w, ringInf (ringDepth d q) w ∂μ) - A.output v) ≤ ε' := by
  refine ⟨⟨p1a d q, p1b d hd q hq1⟩, ?_⟩
  intro ε' hε
  have hτp := tau_pos d q
  have hmeas : ∀ i, Measurable (fun w => (rr d q i w + tau d q) / (2 * tau d q)) :=
    fun i => ((rr_meas d q i).add_const _).div_const _
  have hmem : ∀ i w, (rr d q i w + tau d q) / (2 * tau d q) ∈ Set.Icc (0 : ℝ) 1 := by
    intro i w
    have hb := abs_le.mp (rr_abs d q i w)
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · apply div_nonneg
      · linarith
      · linarith
    · rw [div_le_one (show (0 : ℝ) < 2 * tau d q by linarith)]
      linarith
  by_cases hε2 : ε' ≤ 2
  · refine ⟨⟨fun i w => (rr d q i w + tau d q) / (2 * tau d q), hmeas, hmem,
      fun v i => 2 * tau d q * v i - tau d q⟩, ?_⟩
    intro μ _ hμ v hv
    have herr : ∀ i, |(2 * tau d q * v i - tau d q) - (∫ w, ringInf (ringDepth d q) w ∂μ) i|
        ≤ ε' * (d : ℝ) ^ (-1 / q) := by
      intro i
      rw [int_coord]
      exact coord_err d q ε' hε hε2 μ i (v i) (tau_le d hd q hq1) (hv i)
    refine ⟨fun _ i => herr i, ?_⟩
    apply small_b d hd q hq1 ε' hε
    intro i
    have h := herr i
    rw [abs_sub_comm] at h
    exact h
  · refine ⟨⟨fun i w => (rr d q i w + tau d q) / (2 * tau d q), hmeas, hmem,
      fun _ _ => 0⟩, ?_⟩
    intro μ _ hμ v _
    refine ⟨fun h => absurd h hε2, ?_⟩
    have h1 := big_case d q hq1 μ hμ
      ((∫ w, ringInf (ringDepth d q) w ∂μ) - fun _ => (0 : ℝ)) (fun i => by simp)
    exact le_trans h1 (by linarith)
