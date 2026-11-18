-- Prove2me | solution 1 for OWMR.fifo_prep_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T06:36:58.574938+00:00
-- url     : https://prove2.me/submissions/7e89a398-1a9c-4419-a004-f455d4217a46

import Definitions.Def_owmr_network_model
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
Appendix B, preparation phase: the expected total "size" of the preparation periods is finite.

A preparation period `t` is one with `t + 1 < T₀`, or one in which some retailer `j` has not yet
accumulated demand `b_j` (`S_{j,t} = ∑_{s<t} D_{j,s} < b_j`). On the second event,
`1{S_{j,t} < b_j} ≤ e^{b_j} ∏_{s<t} e^{-D_{j,s}}` (Chernoff), and with `r_j = 𝔼 e^{-D_j} < 1`
(as `𝔼 D_j > 0`) and the product structure of the i.i.d. demand vectors,
`𝔼[(1 + ∑_i S_{i,t}) ∏_{s<t} e^{-D_{j,s}}] ≤ r_j^t + t (∑_i 𝔼 D_i) r_j^{t-1}`, using only first
moments, even though the components of one demand vector may be dependent (one coordinate of
the sequence at a time). Both bounds are summable in `t`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open OWMR

section pi

variable {α : Type} [MeasurableSpace α]

/-- Product formula for the product of i.i.d. coordinates. -/
private lemma lintegral_pi_prod (μ : Measure α) [IsProbabilityMeasure μ] :
    ∀ (N : ℕ) (G : Fin N → α → ℝ≥0∞), (∀ k, Measurable (G k)) →
      ∫⁻ z, ∏ k, G k (z k) ∂(Measure.pi fun _ : Fin N => μ) = ∏ k, ∫⁻ a, G k a ∂μ
  | 0, G, _ => by simp
  | N + 1, G, hG => by
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => μ) 0
    have hF : Measurable fun p : α × (Fin N → α) => G 0 p.1 * ∏ k, G k.succ (p.2 k) :=
      ((hG 0).comp measurable_fst).mul (Finset.measurable_prod _ fun k _ =>
        (hG k.succ).comp ((measurable_pi_apply k).comp measurable_snd))
    have key : ∫⁻ z, ∏ k, G k (z k) ∂(Measure.pi fun _ : Fin (N + 1) => μ)
        = ∫⁻ z, (fun p : α × (Fin N → α) => G 0 p.1 * ∏ k, G k.succ (p.2 k))
            (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => α) 0 z)
            ∂(Measure.pi fun _ : Fin (N + 1) => μ) := by
      refine lintegral_congr fun z => ?_
      simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.prod_univ_succ, Fin.tail]
    rw [key, hmp.lintegral_comp hF, lintegral_prod_mul (f := G 0)
      (g := fun y : Fin N → α => ∏ k, G k.succ (y k)) (hG 0).aemeasurable
      (Finset.measurable_prod _ fun k _ => (hG k.succ).comp (measurable_pi_apply k)).aemeasurable,
      lintegral_pi_prod μ N (fun k => G k.succ) (fun k => hG k.succ), Fin.prod_univ_succ]

variable [Zero α]

private lemma measurable_padHist' (N : ℕ) : Measurable (padHist N : (Fin N → α) → ℕ → α) := by
  refine measurable_pi_lambda _ fun t => ?_
  by_cases h : t < N
  · simp only [padHist, dif_pos h]
    exact measurable_pi_apply _
  · simp only [padHist, dif_neg h]
    exact measurable_const

/-- Products of functions of the first `t` coordinates of the padded history. -/
private lemma lintegral_prod_pad (μ : Measure α) [IsProbabilityMeasure μ] (N t : ℕ) (htN : t ≤ N)
    (H : ℕ → α → ℝ≥0∞) (hH : ∀ s, Measurable (H s)) :
    ∫⁻ z, ∏ s ∈ Finset.range t, H s (padHist N z s) ∂(Measure.pi fun _ : Fin N => μ)
      = ∏ s ∈ Finset.range t, ∫⁻ a, H s a ∂μ := by
  have e1 : ∀ z : Fin N → α, ∏ s ∈ Finset.range t, H s (padHist N z s)
      = ∏ k : Fin N, (if (k : ℕ) < t then H k (z k) else 1) := by
    intro z
    have e2 : ∏ k : Fin N, (if (k : ℕ) < t then H k (z k) else 1)
        = ∏ k : Fin N, (fun s : ℕ => if s < t then H s (padHist N z s) else 1) (k : ℕ) := by
      refine Finset.prod_congr rfl fun k _ => ?_
      simp only
      split_ifs <;> simp [padHist, k.2]
    rw [e2, Fin.prod_univ_eq_prod_range (fun s : ℕ => if s < t then H s (padHist N z s) else 1) N]
    obtain ⟨m, rfl⟩ : ∃ m, N = t + m := ⟨N - t, by omega⟩
    rw [Finset.prod_range_add]
    have h2 : ∏ k ∈ Finset.range m,
        (if t + k < t then H (t + k) (padHist (t + m) z (t + k)) else 1) = 1 :=
      Finset.prod_eq_one fun k _ => if_neg (by omega)
    rw [h2, mul_one]
    exact Finset.prod_congr rfl fun s hs => (if_pos (Finset.mem_range.1 hs)).symm
  simp_rw [e1]
  rw [lintegral_pi_prod μ N (fun k a => if (k : ℕ) < t then H k a else 1) (fun k => by
    split_ifs
    · exact hH k
    · exact measurable_const)]
  rw [Fin.prod_univ_eq_prod_range (fun s => ∫⁻ a, (if s < t then H s a else 1) ∂μ) N]
  obtain ⟨m, rfl⟩ : ∃ m, N = t + m := ⟨N - t, by omega⟩
  rw [Finset.prod_range_add]
  have h2 : ∏ k ∈ Finset.range m, ∫⁻ a, (if t + k < t then H (t + k) a else 1) ∂μ = 1 :=
    Finset.prod_eq_one fun k _ => by simp
  rw [h2, mul_one]
  exact Finset.prod_congr rfl fun s hs => by simp [Finset.mem_range.1 hs]

/-- One coordinate of the padded history has law `μ`. -/
private lemma lintegral_coord_law (μ : Measure α) [IsProbabilityMeasure μ] (N s : ℕ) (hs : s < N)
    (F : α → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F (padHist N z s) ∂(Measure.pi fun _ : Fin N => μ) = ∫⁻ a, F a ∂μ := by
  have e : ∀ z : Fin N → α, padHist N z s = z ⟨s, hs⟩ := fun z => by simp [padHist, hs]
  simp_rw [e]
  exact (measurePreserving_eval (fun _ : Fin N => μ) (⟨s, hs⟩ : Fin N)).lintegral_comp hF

end pi

/-- `𝔼 e^{-D_j} < 1` when `𝔼 D_j > 0`. -/
private lemma exp_moment_lt_one {n : ℕ} (μ : Measure (Fin n → ℝ≥0)) [IsProbabilityMeasure μ] (j : Fin n)
    (hpos : 0 < ∫⁻ a, (a j : ℝ≥0∞) ∂μ) :
    ∫⁻ a, ENNReal.ofReal (Real.exp (-((a j : ℝ≥0) : ℝ))) ∂μ < 1 := by
  set E : (Fin n → ℝ≥0) → ℝ≥0∞ := fun a => ENNReal.ofReal (Real.exp (-((a j : ℝ≥0) : ℝ))) with hE
  have hEm : Measurable E :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_pi_apply j).coe_nnreal_real.neg)
  have hE1 : ∀ a, E a ≤ 1 := fun a => by
    simp only [hE]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.2 (by linarith [NNReal.coe_nonneg (a j)]))
  have hsupp : Function.support (fun a : Fin n → ℝ≥0 => (a j : ℝ≥0∞))
      = Function.support (fun a => 1 - E a) := by
    ext a
    simp only [Function.mem_support, ne_eq, ENNReal.coe_eq_zero]
    constructor
    · intro h
      have hpos' : (0 : ℝ) < (a j : ℝ) := by
        have : 0 < a j := pos_iff_ne_zero.2 h
        exact_mod_cast this
      have : E a < 1 := by
        simp only [hE]
        rw [← ENNReal.ofReal_one]
        exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (Real.exp_lt_one_iff.2 (by linarith))
      exact (tsub_pos_of_lt this).ne'
    · intro h h0
      apply h
      simp [hE, h0]
  have h1 : 0 < ∫⁻ a, (1 - E a) ∂μ := by
    rw [lintegral_pos_iff_support (f := fun a => 1 - E a) (measurable_const.sub hEm), ← hsupp]
    rwa [← lintegral_pos_iff_support (measurable_pi_apply j).coe_nnreal_ennreal]
  rw [lintegral_sub hEm (by
      refine ne_top_of_le_ne_top (b := ∫⁻ _a, (1 : ℝ≥0∞) ∂μ) (by simp) (lintegral_mono hE1))
      (ae_of_all _ hE1), lintegral_const, measure_univ, one_mul] at h1
  exact (tsub_pos_iff_lt.1 h1)

/-- `∑_{t<T} t r^{t-1}` is bounded when `r < 1`. -/
private lemma sum_mul_geom_bdd (r : ℝ≥0∞) (hr : r < 1) :
    ∃ Q : ℝ≥0∞, Q ≠ ∞ ∧ ∀ T, ∑ t ∈ Finset.range T, (t : ℝ≥0∞) * r ^ (t - 1) ≤ Q := by
  have hrt : r ≠ ∞ := ne_top_of_lt hr
  set r' := r.toReal with hr'
  have hr'0 : 0 ≤ r' := ENNReal.toReal_nonneg
  have hr'1 : r' < 1 := by
    have := ENNReal.toReal_strict_mono ENNReal.one_ne_top hr
    simpa using this
  have hrr : r = ENNReal.ofReal r' := (ENNReal.ofReal_toReal hrt).symm
  set f : ℕ → ℝ := fun t => (t : ℝ) * r' ^ (t - 1) with hf
  have hf0 : ∀ t, 0 ≤ f t := fun t => mul_nonneg (Nat.cast_nonneg t) (pow_nonneg hr'0 _)
  have hsum : Summable f := by
    rw [← summable_nat_add_iff 1]
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (show ‖r'‖ < 1 by
      rw [Real.norm_eq_abs, abs_of_nonneg hr'0]; exact hr'1)
    have h2 := summable_geometric_of_lt_one hr'0 hr'1
    refine (h1.add h2).congr fun t => ?_
    simp only [hf, pow_one, Nat.cast_add, Nat.cast_one, add_tsub_cancel_right]
    ring
  refine ⟨ENNReal.ofReal (∑' t, f t), ENNReal.ofReal_ne_top, fun T => ?_⟩
  have e : ∀ t : ℕ, ((t : ℕ) : ℝ≥0∞) * r ^ (t - 1) = ENNReal.ofReal (f t) := fun t => by
    rw [hrr, ← ENNReal.ofReal_pow hr'0, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul
      (Nat.cast_nonneg t)]
  simp only [e]
  rw [← ENNReal.ofReal_sum_of_nonneg fun t _ => hf0 t]
  exact ENNReal.ofReal_le_ofReal (hsum.sum_le_tsum _ fun t _ => hf0 t)

theorem solution {n : ℕ} (μ : Measure (Fin n → ℝ≥0)) [IsProbabilityMeasure μ]
    (hpos : ∀ i, 0 < ∫⁻ a, (a i : ℝ≥0∞) ∂μ) (hfin : ∀ i, ∫⁻ a, (a i : ℝ≥0∞) ∂μ < ∞)
    (T0 : ℕ) (b : Fin n → ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ T N : ℕ, T ≤ N →
      ∫⁻ z, ∑ t ∈ Finset.range T,
        (if T0 ≤ t + 1 ∧ ∀ i, b i ≤ ∑ s ∈ Finset.range t, ((padHist N z s i : ℝ≥0) : ℝ) then 0
          else ENNReal.ofReal (1 + ∑ i, ∑ s ∈ Finset.range t, ((padHist N z s i : ℝ≥0) : ℝ)))
        ∂(Measure.pi fun _ : Fin N => μ) ≤ C := by
  set m : Fin n → ℝ≥0∞ := fun i => ∫⁻ a, (a i : ℝ≥0∞) ∂μ with hm
  set mm : ℝ≥0∞ := ∑ i, m i with hmm
  have hmmf : mm ≠ ∞ := ENNReal.sum_ne_top.2 fun i _ => (hfin i).ne
  set E : Fin n → (Fin n → ℝ≥0) → ℝ≥0∞ := fun j a => ENNReal.ofReal (Real.exp (-((a j : ℝ≥0) : ℝ)))
    with hE
  have hEm : ∀ j, Measurable (E j) := fun j =>
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_pi_apply j).coe_nnreal_real.neg)
  have hE1 : ∀ j a, E j a ≤ 1 := fun j a => by
    simp only [hE]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.2 (by linarith [NNReal.coe_nonneg (a j)]))
  set r : Fin n → ℝ≥0∞ := fun j => ∫⁻ a, E j a ∂μ with hr
  have hr1 : ∀ j, r j < 1 := fun j => exp_moment_lt_one μ j (hpos j)
  choose Q hQf hQ using fun j => sum_mul_geom_bdd (r j) (hr1 j)
  -- notation for the history
  have hD := fun N => measurable_padHist' (α := Fin n → ℝ≥0) N
  set A : (N : ℕ) → ℕ → (Fin N → Fin n → ℝ≥0) → ℝ≥0∞ := fun N t z =>
    1 + ∑ i, ∑ s ∈ Finset.range t, ((padHist N z s i : ℝ≥0) : ℝ≥0∞) with hA
  have hAeq : ∀ N t (z : Fin N → Fin n → ℝ≥0),
      ENNReal.ofReal (1 + ∑ i, ∑ s ∈ Finset.range t, ((padHist N z s i : ℝ≥0) : ℝ))
      = A N t z := by
    intro N t z
    rw [ENNReal.ofReal_add zero_le_one (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun s _ =>
      NNReal.coe_nonneg _), ENNReal.ofReal_one, ENNReal.ofReal_sum_of_nonneg fun i _ =>
      Finset.sum_nonneg fun s _ => NNReal.coe_nonneg _]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun s _ => NNReal.coe_nonneg _]
    exact Finset.sum_congr rfl fun s _ => ENNReal.ofReal_coe_nnreal
  have hAm : ∀ N t, Measurable (A N t) := fun N t =>
    measurable_const.add (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun s _ =>
      ((measurable_pi_apply i).comp ((measurable_pi_apply s).comp (hD N))).coe_nnreal_ennreal)
  set B : (N : ℕ) → ℕ → Fin n → (Fin N → Fin n → ℝ≥0) → ℝ≥0∞ := fun N t j z =>
    ∏ s ∈ Finset.range t, E j (padHist N z s) with hB
  have hBm : ∀ N t j, Measurable (B N t j) := fun N t j =>
    Finset.measurable_prod _ fun s _ => (hEm j).comp ((measurable_pi_apply s).comp (hD N))
  -- expectations
  have hEA : ∀ N t, t ≤ N → ∫⁻ z, A N t z ∂(Measure.pi fun _ : Fin N => μ) = 1 + t * mm := by
    intro N t htN
    simp only [hA]
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_finsetSum (f := fun i (z : Fin N → Fin n → ℝ≥0) =>
          ∑ s ∈ Finset.range t, ((padHist N z s i : ℝ≥0) : ℝ≥0∞))
        _ fun i _ => Finset.measurable_sum _ fun s _ =>
      ((measurable_pi_apply i).comp ((measurable_pi_apply s).comp (hD N))).coe_nnreal_ennreal]
    congr 1
    rw [hmm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_finsetSum (f := fun s (z : Fin N → Fin n → ℝ≥0) => ((padHist N z s i : ℝ≥0) : ℝ≥0∞))
      _ fun s _ =>
      ((measurable_pi_apply i).comp ((measurable_pi_apply s).comp (hD N))).coe_nnreal_ennreal]
    rw [Finset.sum_congr rfl fun s hs => lintegral_coord_law μ N s
      (by have := Finset.mem_range.1 hs; omega) (fun a => (a i : ℝ≥0∞))
      (measurable_pi_apply i).coe_nnreal_ennreal]
    simp [hm]
  have hEB : ∀ N t j, t ≤ N → ∫⁻ z, A N t z * B N t j z ∂(Measure.pi fun _ : Fin N => μ)
      ≤ r j ^ t + t * mm * r j ^ (t - 1) := by
    intro N t j htN
    have hBt : ∫⁻ z, B N t j z ∂(Measure.pi fun _ : Fin N => μ) = r j ^ t := by
      simp only [hB]
      rw [lintegral_prod_pad μ N t htN (fun _ => E j) (fun _ => hEm j)]
      simp [hr]
    have hterm : ∀ i, ∀ s' ∈ Finset.range t,
        ∫⁻ z : Fin N → Fin n → ℝ≥0, ((padHist N z s' i : ℝ≥0) : ℝ≥0∞) * B N t j z
          ∂(Measure.pi fun _ : Fin N => μ)
          ≤ m i * r j ^ (t - 1) := by
      intro i s' hs'
      set H : ℕ → (Fin n → ℝ≥0) → ℝ≥0∞ := fun s a =>
        if s = s' then (a i : ℝ≥0∞) * E j a else E j a with hH
      have hHm : ∀ s, Measurable (H s) := fun s => by
        simp only [hH]; split_ifs
        · exact (measurable_pi_apply i).coe_nnreal_ennreal.mul (hEm j)
        · exact hEm j
      have e1 : ∀ z : Fin N → Fin n → ℝ≥0, ((padHist N z s' i : ℝ≥0) : ℝ≥0∞) * B N t j z
          = ∏ s ∈ Finset.range t, H s (padHist N z s) := by
        intro z
        simp only [hB]
        rw [← Finset.mul_prod_erase _ _ hs', ← Finset.mul_prod_erase (Finset.range t)
          (fun s => H s (padHist N z s)) hs']
        have e2 : ∏ s ∈ (Finset.range t).erase s', H s (padHist N z s)
            = ∏ s ∈ (Finset.range t).erase s', E j (padHist N z s) :=
          Finset.prod_congr rfl fun s hs => by simp [hH, Finset.ne_of_mem_erase hs]
        rw [e2]
        simp [hH, mul_assoc]
      simp_rw [e1]
      rw [lintegral_prod_pad μ N t htN H hHm, ← Finset.mul_prod_erase _ _ hs']
      have e3 : ∏ s ∈ (Finset.range t).erase s', ∫⁻ a, H s a ∂μ = r j ^ (t - 1) := by
        rw [Finset.prod_congr rfl fun s hs => by
          show ∫⁻ a, H s a ∂μ = r j
          simp [hH, Finset.ne_of_mem_erase hs, hr]]
        rw [Finset.prod_const, Finset.card_erase_of_mem hs', Finset.card_range]
      rw [e3]
      gcongr
      simp only [hH, if_true]
      calc ∫⁻ a, (a i : ℝ≥0∞) * E j a ∂μ ≤ ∫⁻ a, (a i : ℝ≥0∞) ∂μ :=
            lintegral_mono fun a => by
              calc (a i : ℝ≥0∞) * E j a ≤ (a i : ℝ≥0∞) * 1 := by gcongr; exact hE1 j a
                _ = _ := mul_one _
        _ = m i := rfl
    have hsplit : ∀ z : Fin N → Fin n → ℝ≥0, A N t z * B N t j z = B N t j z
        + ∑ i, ∑ s ∈ Finset.range t, ((padHist N z s i : ℝ≥0) : ℝ≥0∞) * B N t j z := by
      intro z
      simp only [hA, add_mul, one_mul, Finset.sum_mul]
    simp_rw [hsplit]
    rw [lintegral_add_left (hBm N t j), hBt, lintegral_finsetSum (f := fun i (z : Fin N → Fin n → ℝ≥0) =>
      ∑ s ∈ Finset.range t, ((padHist N z s i : ℝ≥0) : ℝ≥0∞) * B N t j z) _ fun i _ =>
      Finset.measurable_sum _ fun s _ => (((measurable_pi_apply i).comp ((measurable_pi_apply s).comp
        (hD N))).coe_nnreal_ennreal).mul (hBm N t j)]
    gcongr
    calc ∑ i, ∫⁻ z, ∑ s ∈ Finset.range t, ((padHist N z s i : ℝ≥0) : ℝ≥0∞) * B N t j z
          ∂(Measure.pi fun _ : Fin N => μ)
        = ∑ i, ∑ s ∈ Finset.range t, ∫⁻ z, ((padHist N z s i : ℝ≥0) : ℝ≥0∞) * B N t j z
          ∂(Measure.pi fun _ : Fin N => μ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [lintegral_finsetSum (f := fun s (z : Fin N → Fin n → ℝ≥0) =>
              ((padHist N z s i : ℝ≥0) : ℝ≥0∞) * B N t j z) _
            fun s _ => (((measurable_pi_apply i).comp
            ((measurable_pi_apply s).comp (hD N))).coe_nnreal_ennreal).mul (hBm N t j)]
      _ ≤ ∑ i, ∑ _s ∈ Finset.range t, m i * r j ^ (t - 1) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun s hs => hterm i s hs
      _ = t * mm * r j ^ (t - 1) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hmm, Finset.sum_mul,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
  -- the pointwise bound
  have hpt : ∀ N t (z : Fin N → Fin n → ℝ≥0),
      (if T0 ≤ t + 1 ∧ ∀ i, b i ≤ ∑ s ∈ Finset.range t, ((padHist N z s i : ℝ≥0) : ℝ) then 0
        else ENNReal.ofReal (1 + ∑ i, ∑ s ∈ Finset.range t, ((padHist N z s i : ℝ≥0) : ℝ)))
      ≤ (if t + 1 < T0 then A N t z else 0)
        + ∑ j, ENNReal.ofReal (Real.exp (b j)) * (A N t z * B N t j z) := by
    intro N t z
    split_ifs with h1 h2
    · exact zero_le
    · exact zero_le
    · rw [hAeq]; exact le_self_add
    · rw [zero_add, hAeq]
      have : ∃ j, ∑ s ∈ Finset.range t, ((padHist N z s j : ℝ≥0) : ℝ) < b j := by
        by_contra hc
        simp only [not_exists, not_lt] at hc
        exact h1 ⟨by omega, hc⟩
      obtain ⟨j, hj⟩ := this
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => ENNReal.ofReal (Real.exp (b j))
        * (A N t z * B N t j z)) (fun j _ => zero_le) (Finset.mem_univ j))
      have hexp : ENNReal.ofReal (Real.exp (b j)) * B N t j z
          = ENNReal.ofReal (Real.exp (b j - ∑ s ∈ Finset.range t, ((padHist N z s j : ℝ≥0) : ℝ))) := by
        simp only [hB, hE]
        rw [← ENNReal.ofReal_prod_of_nonneg fun s _ => (Real.exp_pos _).le, ← ENNReal.ofReal_mul
          (Real.exp_pos _).le, sub_eq_add_neg, Real.exp_add, ← Finset.sum_neg_distrib, Real.exp_sum]
      calc A N t z = A N t z * 1 := (mul_one _).symm
        _ ≤ A N t z * ENNReal.ofReal (Real.exp (b j
            - ∑ s ∈ Finset.range t, ((padHist N z s j : ℝ≥0) : ℝ))) := by
            gcongr
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by linarith))
        _ = ENNReal.ofReal (Real.exp (b j)) * (A N t z * B N t j z) := by
            rw [← hexp]; ring
  -- summing up
  set C : ℝ≥0∞ := ∑ t ∈ Finset.range T0, (1 + t * mm)
    + ∑ j, ENNReal.ofReal (Real.exp (b j)) * ((1 - r j)⁻¹ + mm * Q j) with hC
  refine ⟨C, ?_, fun T N hTN => ?_⟩
  · refine ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun t _ =>
      ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top (ENNReal.natCast_ne_top t) hmmf⟩,
      ENNReal.sum_ne_top.2 fun j _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.2 ⟨ENNReal.inv_ne_top.2 (tsub_pos_of_lt (hr1 j)).ne',
          ENNReal.mul_ne_top hmmf (hQf j)⟩)⟩
  calc ∫⁻ z, ∑ t ∈ Finset.range T,
        (if T0 ≤ t + 1 ∧ ∀ i, b i ≤ ∑ s ∈ Finset.range t, ((padHist N z s i : ℝ≥0) : ℝ) then 0
          else ENNReal.ofReal (1 + ∑ i, ∑ s ∈ Finset.range t, ((padHist N z s i : ℝ≥0) : ℝ)))
        ∂(Measure.pi fun _ : Fin N => μ)
      ≤ ∫⁻ z, ∑ t ∈ Finset.range T, ((if t + 1 < T0 then A N t z else 0)
          + ∑ j, ENNReal.ofReal (Real.exp (b j)) * (A N t z * B N t j z))
          ∂(Measure.pi fun _ : Fin N => μ) :=
        lintegral_mono fun z => Finset.sum_le_sum fun t _ => hpt N t z
    _ = ∑ t ∈ Finset.range T, ((if t + 1 < T0 then ∫⁻ z, A N t z ∂(Measure.pi fun _ : Fin N => μ) else 0)
          + ∑ j, ENNReal.ofReal (Real.exp (b j))
            * ∫⁻ z, A N t z * B N t j z ∂(Measure.pi fun _ : Fin N => μ)) := by
        rw [lintegral_finsetSum _ fun t _ => (by
          split_ifs
          · exact (hAm N t).add (Finset.measurable_sum _ fun j _ =>
              measurable_const.mul ((hAm N t).mul (hBm N t j)))
          · exact measurable_const.add (Finset.measurable_sum _ fun j _ =>
              measurable_const.mul ((hAm N t).mul (hBm N t j))))]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [lintegral_add_left (by split_ifs; exacts [hAm N t, measurable_const]),
          lintegral_finsetSum (f := fun j z => ENNReal.ofReal (Real.exp (b j)) * (A N t z * B N t j z))
            _ fun j _ => measurable_const.mul ((hAm N t).mul (hBm N t j))]
        congr 1
        · split_ifs <;> simp
        · exact Finset.sum_congr rfl fun j _ => lintegral_const_mul _ ((hAm N t).mul (hBm N t j))
    _ ≤ ∑ t ∈ Finset.range T, ((if t + 1 < T0 then 1 + t * mm else 0)
          + ∑ j, ENNReal.ofReal (Real.exp (b j)) * (r j ^ t + t * mm * r j ^ (t - 1))) := by
        refine Finset.sum_le_sum fun t ht => ?_
        have htN : t ≤ N := by have := Finset.mem_range.1 ht; omega
        gcongr with j
        · split_ifs
          · exact (hEA N t htN).le
          · exact le_rfl
        · exact hEB N t j htN
    _ = ∑ t ∈ Finset.range T, (if t + 1 < T0 then 1 + t * mm else 0)
          + ∑ j, ENNReal.ofReal (Real.exp (b j)) * (∑ t ∈ Finset.range T, r j ^ t
            + mm * ∑ t ∈ Finset.range T, (t : ℝ≥0∞) * r j ^ (t - 1)) := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun t _ => ?_
        ring
    _ ≤ C := by
        rw [hC]
        gcongr with j
        · calc ∑ t ∈ Finset.range T, (if t + 1 < T0 then 1 + (t : ℝ≥0∞) * mm else 0)
              ≤ ∑ t ∈ Finset.range T0, (if t + 1 < T0 then 1 + (t : ℝ≥0∞) * mm else 0) := by
                rw [← Finset.sum_range_add_sum_Ico _ (min_le_left T T0),
                  ← Finset.sum_range_add_sum_Ico _ (min_le_right T T0)]
                have h0 : ∑ t ∈ Finset.Ico (min T T0) T, (if t + 1 < T0 then 1 + (t : ℝ≥0∞) * mm else 0)
                    = 0 := Finset.sum_eq_zero fun t ht => by
                  have h1 := (Finset.mem_Ico.1 ht).1
                  have h2 := (Finset.mem_Ico.1 ht).2
                  rw [if_neg (by rcases le_total T T0 with h | h <;> simp [h] at h1 <;> omega)]
                rw [h0, add_zero]
                exact le_self_add
            _ ≤ ∑ t ∈ Finset.range T0, (1 + (t : ℝ≥0∞) * mm) :=
                Finset.sum_le_sum fun t _ => by split_ifs <;> simp
        · calc ∑ t ∈ Finset.range T, r j ^ t ≤ ∑' t, r j ^ t := ENNReal.sum_le_tsum _
            _ = (1 - r j)⁻¹ := ENNReal.tsum_geometric _
        · exact hQ j T
