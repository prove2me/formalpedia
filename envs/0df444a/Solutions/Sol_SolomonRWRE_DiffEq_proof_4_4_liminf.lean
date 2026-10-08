-- Prove2me | solution 1 for SolomonRWRE.DiffEq.proof_4_4_liminf
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:04:53.719592+00:00
-- url     : https://prove2.me/submissions/db2c0c3a-51cf-40b1-8126-a4c53bd094c8

import Mathlib
import Definitions.Def_SolomonRWRE_DiffEq_System

open MeasureTheory ProbabilityTheory Filter Topology


namespace SolomonRWRE.DiffEq

/-- block product `σ_{j+1} ⋯ σ_{j+k}` -/
def W {Ω : Type*} (σ : ℕ → Ω → ℝ) (k j : ℕ) (ω : Ω) : ℝ :=
  ∏ i ∈ Finset.range k, σ (j + i + 1) ω

theorem Y_eq_sum_W {Ω : Type*} (σ : ℕ → Ω → ℝ) (k n : ℕ) (ω : Ω) :
    Y σ k n ω = ∑ j ∈ Finset.range (n + 1 - k), W σ k j ω := by
  unfold Y W
  refine Finset.sum_nbij' (fun j => j - 1) (fun j => j + 1) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢; omega
  · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢; omega
  · intro j hj; simp only [Finset.mem_Icc, Finset.coe_Icc, Set.mem_Icc] at hj; omega
  · intro j hj; simp only [Finset.mem_range, Finset.coe_range, Set.mem_Iio] at hj; omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    refine Finset.prod_nbij' (fun i => i - j) (fun i => j - 1 + i + 1) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢; omega
    · intro i hi; simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢; omega
    · intro i hi; simp only [Finset.mem_Icc, Finset.coe_Icc, Set.mem_Icc] at hi; omega
    · intro i hi; simp only [Finset.mem_range, Finset.coe_range, Set.mem_Iio] at hi; omega
    · intro i hi
      simp only [Finset.mem_Icc] at hi
      congr 2
      omega

theorem sandwich_core (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (k : ℕ) (hk : 1 ≤ k) (c : ℝ)
    (hr : ∀ r < k, Tendsto (fun Q : ℕ => (∑ q ∈ Finset.range Q, a (k * q + r)) / Q) atTop
      (𝓝 c)) :
    Tendsto (fun n : ℕ => (∑ j ∈ Finset.range (n + 1 - k), a j) / n) atTop (𝓝 c) := by
  have hA : ∀ Q, ∑ j ∈ Finset.range (k * Q), a j =
      ∑ r ∈ Finset.range k, ∑ q ∈ Finset.range Q, a (k * q + r) := by
    intro Q
    induction Q with
    | zero => simp
    | succ Q ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      simp_rw [Finset.sum_range_succ]
      rw [Finset.sum_add_distrib]
  have hAlim : Tendsto (fun Q : ℕ => (∑ j ∈ Finset.range (k * Q), a j) / Q) atTop
      (𝓝 (k * c)) := by
    have := tendsto_finset_sum (Finset.range k) (fun r hr' => hr r (Finset.mem_range.1 hr'))
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    refine this.congr fun Q => ?_
    rw [hA, Finset.sum_div]
  have hkpos : 0 < k := hk
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set Q : ℕ → ℕ := fun n => (n + 1 - k) / k with hQdef
  have hQ : Tendsto Q atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨k * b + k, fun n hn => ?_⟩
    simp only [hQdef]
    rw [Nat.le_div_iff_mul_le hkpos, mul_comm]
    omega
  have hQ1 : Tendsto (fun n => Q n + 1) atTop atTop := (tendsto_add_atTop_nat 1).comp hQ
  have hL : Tendsto (fun n => ((∑ j ∈ Finset.range (k * Q n), a j) / (Q n : ℝ)) *
      (((Q n : ℝ) / ((Q n : ℝ) + 2)) / k)) atTop (𝓝 c) := by
    have := (hAlim.comp hQ).mul (((tendsto_natCast_div_add_atTop (2 : ℝ)).comp hQ).div_const
      (k : ℝ))
    rw [show (k : ℝ) * c * (1 / k) = c by field_simp] at this
    exact this
  have hU : Tendsto (fun n => ((∑ j ∈ Finset.range (k * (Q n + 1)), a j) / ((Q n + 1 : ℕ) : ℝ)) *
      ((((Q n + 1 : ℕ) : ℝ) / (((Q n + 1 : ℕ) : ℝ) + (-(1 / (k : ℝ))))) / k)) atTop (𝓝 c) := by
    have := (hAlim.comp hQ1).mul (((tendsto_natCast_div_add_atTop (-(1 / (k : ℝ)))).comp hQ1).div_const
      (k : ℝ))
    rw [show (k : ℝ) * c * (1 / k) = c by field_simp] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU ?_ ?_
  · rw [eventually_atTop]
    refine ⟨2 * k, fun n hn => ?_⟩
    have h1 : k * Q n ≤ n + 1 - k := Nat.mul_div_le (n + 1 - k) k
    have h2 : n + 1 - k < k * (Q n + 1) := Nat.lt_mul_div_succ (n + 1 - k) hkpos
    have hQpos : 0 < Q n := Nat.div_pos (by omega) hkpos
    have hQr : (1 : ℝ) ≤ Q n := by exact_mod_cast hQpos
    have h2r : (n : ℝ) ≤ k * ((Q n : ℝ) + 2) := by
      have : n ≤ k * (Q n + 2) := by rw [Nat.mul_succ] at h2; rw [Nat.mul_add]; omega
      exact_mod_cast this
    have hS : ∑ j ∈ Finset.range (k * Q n), a j ≤ ∑ j ∈ Finset.range (n + 1 - k), a j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h1) (fun j _ _ => ha j)
    have hS0 : 0 ≤ ∑ j ∈ Finset.range (k * Q n), a j := Finset.sum_nonneg fun j _ => ha j
    have heq : ((∑ j ∈ Finset.range (k * Q n), a j) / (Q n : ℝ)) *
        (((Q n : ℝ) / ((Q n : ℝ) + 2)) / k) =
        (∑ j ∈ Finset.range (k * Q n), a j) / (k * ((Q n : ℝ) + 2)) := by
      field_simp
    rw [heq]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    calc (∑ j ∈ Finset.range (k * Q n), a j) / (k * ((Q n : ℝ) + 2))
        ≤ (∑ j ∈ Finset.range (k * Q n), a j) / n := div_le_div_of_nonneg_left hS0 hnpos h2r
      _ ≤ _ := div_le_div_of_nonneg_right hS hnpos.le
  · rw [eventually_atTop]
    refine ⟨2 * k, fun n hn => ?_⟩
    have h1 : k * Q n ≤ n + 1 - k := Nat.mul_div_le (n + 1 - k) k
    have h2 : n + 1 - k < k * (Q n + 1) := Nat.lt_mul_div_succ (n + 1 - k) hkpos
    have hQpos : 0 < Q n := Nat.div_pos (by omega) hkpos
    have hQr : (1 : ℝ) ≤ Q n := by exact_mod_cast hQpos
    have hkQ : (1 : ℝ) ≤ k * Q n := one_le_mul_of_one_le_of_one_le hkr hQr
    have h1r : (k : ℝ) * (Q n + 1) - 1 ≤ n := by
      have : k * Q n + k - 1 ≤ n := by omega
      have h' : ((k * Q n + k - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
      rw [Nat.cast_sub (by omega)] at h'
      push_cast at h'
      linarith
    have hS : ∑ j ∈ Finset.range (n + 1 - k), a j ≤ ∑ j ∈ Finset.range (k * (Q n + 1)), a j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h2.le) (fun j _ _ => ha j)
    have hS0 : 0 ≤ ∑ j ∈ Finset.range (k * (Q n + 1)), a j := Finset.sum_nonneg fun j _ => ha j
    have hden : (0 : ℝ) < k * ((Q n : ℝ) + 1) - 1 := by nlinarith
    have heq : ((∑ j ∈ Finset.range (k * (Q n + 1)), a j) / ((Q n + 1 : ℕ) : ℝ)) *
        ((((Q n + 1 : ℕ) : ℝ) / (((Q n + 1 : ℕ) : ℝ) + (-(1 / (k : ℝ))))) / k) =
        (∑ j ∈ Finset.range (k * (Q n + 1)), a j) / (k * ((Q n : ℝ) + 1) - 1) := by
      push_cast
      have hk0 : (k : ℝ) ≠ 0 := by positivity
      have hne : (Q n : ℝ) + 1 + -(1 / (k : ℝ)) ≠ 0 := by
        rw [← sub_eq_add_neg]; apply ne_of_gt
        have : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact hkr
        linarith
      field_simp
      ring
    rw [heq]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    calc (∑ j ∈ Finset.range (n + 1 - k), a j) / (n : ℝ)
        ≤ (∑ j ∈ Finset.range (k * (Q n + 1)), a j) / n := div_le_div_of_nonneg_right hS hnpos.le
      _ ≤ _ := div_le_div_of_nonneg_left hS0 hden h1r


section prob

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (σ : ℕ → Ω → ℝ) (hσ : IsIIDNonneg P σ) (k : ℕ)

include hσ

theorem W_nonneg (j : ℕ) (ω : Ω) : 0 ≤ W σ k j ω :=
  Finset.prod_nonneg fun i _ => hσ.nonneg _ ω

theorem W_meas (j : ℕ) : Measurable (W σ k j) :=
  Finset.measurable_prod _ fun i _ => hσ.meas _

theorem lint_sigma (m : ℕ) : ∫⁻ ω, ENNReal.ofReal (σ (m + 1) ω) ∂P = nu P σ :=
  ((hσ.ident m).comp ENNReal.measurable_ofReal).lintegral_eq

theorem W_lintegral (j : ℕ) : ∫⁻ ω, ENNReal.ofReal (W σ k j ω) ∂P = nu P σ ^ k := by
  have hind : iIndepFun (fun i : ℕ => fun ω => ENNReal.ofReal (σ (j + i + 1) ω)) P := by
    have h1 : iIndepFun (fun m : ℕ => fun ω => ENNReal.ofReal (σ (m + 1) ω)) P :=
      hσ.indep.comp (fun _ => ENNReal.ofReal) (fun _ => ENNReal.measurable_ofReal)
    exact h1.precomp (g := fun i : ℕ => j + i) (add_right_injective j)
  unfold W
  simp_rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hσ.nonneg _ _)]
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _ hind
    (fun i => ENNReal.measurable_ofReal.comp (hσ.meas _))]
  simp [lint_sigma P σ hσ]

theorem W_identDistrib (j : ℕ) : IdentDistrib (W σ k j) (W σ k 0) P P := by
  have hmap : ∀ j : ℕ, P.map (fun ω (i : Fin k) => σ (j + i + 1) ω) =
      Measure.pi (fun _ : Fin k => P.map (σ 1)) := by
    intro j
    have hind : iIndepFun (fun i : Fin k => σ (j + i + 1)) P :=
      hσ.indep.precomp (g := fun i : Fin k => j + (i : ℕ))
        ((add_right_injective j).comp Fin.val_injective)
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hσ.meas _).aemeasurable)).1 hind]
    congr 1
    funext i
    exact (hσ.ident _).map_eq
  have hT : IdentDistrib (fun ω (i : Fin k) => σ (j + i + 1) ω)
      (fun ω (i : Fin k) => σ (0 + i + 1) ω) P P :=
    ⟨(measurable_pi_lambda _ fun i => hσ.meas _).aemeasurable,
     (measurable_pi_lambda _ fun i => hσ.meas _).aemeasurable, by rw [hmap j, hmap 0]⟩
  have := hT.comp (u := fun v : Fin k → ℝ => ∏ i, v i)
    (Finset.measurable_prod _ fun i _ => measurable_pi_apply i)
  convert this using 1 <;>
  · funext ω
    simp only [Function.comp, W]
    exact (Fin.prod_univ_eq_prod_range (fun i => σ (_ + i + 1) ω) k).symm

theorem W_indepFun (r : ℕ) {q q' : ℕ} (hqq' : q ≠ q') :
    IndepFun (W σ k (k * q + r)) (W σ k (k * q' + r)) P := by
  let S : ℕ → Finset ℕ := fun a => (Finset.range k).map (addLeftEmbedding a)
  have hW : ∀ a, W σ k a = (fun v : S a → ℝ => ∏ i, v i) ∘ (fun ω (i : S a) => σ (i + 1) ω) := by
    intro a
    funext ω
    simp only [Function.comp, W]
    rw [Finset.prod_coe_sort (S a) (fun i => σ (i + 1) ω), Finset.prod_map]
    rfl
  have hdisj : Disjoint (S (k * q + r)) (S (k * q' + r)) := by
    have hk : k * q + k ≤ k * q' ∨ k * q' + k ≤ k * q := by
      rcases lt_or_gt_of_ne hqq' with h | h
      · left; have := Nat.mul_le_mul_left k h; rw [Nat.mul_succ] at this; exact this
      · right; have := Nat.mul_le_mul_left k h; rw [Nat.mul_succ] at this; exact this
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [S, Finset.mem_map, Finset.mem_range, addLeftEmbedding_apply] at hi hi'
    obtain ⟨x, hx, rfl⟩ := hi
    obtain ⟨y, hy, hxy⟩ := hi'
    omega
  rw [hW, hW]
  exact (hσ.indep.indepFun_finset _ _ hdisj hσ.meas).comp
    (Finset.measurable_prod _ fun i _ => measurable_pi_apply i)
    (Finset.measurable_prod _ fun i _ => measurable_pi_apply i)

theorem W_integrable (hν : nu P σ < ⊤) (j : ℕ) : Integrable (W σ k j) P :=
  ⟨(W_meas P σ hσ k j).aestronglyMeasurable,
   (hasFiniteIntegral_iff_ofReal (ae_of_all _ (W_nonneg P σ hσ k j))).2
     (by rw [W_lintegral P σ hσ]; exact ENNReal.pow_lt_top hν)⟩

theorem W_integral (hν : nu P σ < ⊤) (j : ℕ) : ∫ ω, W σ k j ω ∂P = (nu P σ).toReal ^ k := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (W_nonneg P σ hσ k j))
    (W_meas P σ hσ k j).aestronglyMeasurable, W_lintegral P σ hσ, ENNReal.toReal_pow]

theorem slln_residue (hν : nu P σ < ⊤) (r : ℕ) :
    ∀ᵐ ω ∂P, Tendsto (fun Q : ℕ => (∑ q ∈ Finset.range Q, W σ k (k * q + r) ω) / Q) atTop
      (𝓝 ((nu P σ).toReal ^ k)) := by
  have := strong_law_ae_real (fun q => W σ k (k * q + r)) (W_integrable P σ hσ k hν _)
    (fun q q' hqq' => W_indepFun P σ hσ k r hqq')
    (fun q => (W_identDistrib P σ hσ k _).trans (W_identDistrib P σ hσ k _).symm)
  rw [W_integral P σ hσ k hν] at this
  exact this

theorem block_avg_finite (hk : 1 ≤ k) (hν : nu P σ < ⊤) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ENNReal.ofReal (Y σ k n ω / n)) atTop (𝓝 (nu P σ ^ k)) := by
  have h := ae_all_iff.2 (fun r : ℕ => slln_residue P σ hσ k hν r)
  filter_upwards [h] with ω hω
  have h1 := sandwich_core (fun j => W σ k j ω) (fun j => W_nonneg P σ hσ k j ω) k hk _
    (fun r _ => hω r)
  have h2 := ENNReal.tendsto_ofReal h1
  simp_rw [Y_eq_sum_W]
  rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hν.ne] at h2
  exact h2

theorem truncated_iid (M : ℕ) : IsIIDNonneg P (fun n ω => min (σ n ω) M) where
  meas n := (hσ.meas n).min measurable_const
  nonneg n ω := le_min (hσ.nonneg n ω) (Nat.cast_nonneg M)
  indep := hσ.indep.comp (fun _ x => min x M) (fun _ => measurable_id.min measurable_const)
  ident n := (hσ.ident n).comp (measurable_id.min measurable_const)

theorem nu_trunc_lt_top (M : ℕ) : nu P (fun n ω => min (σ n ω) M) < ⊤ := by
  unfold nu
  calc ∫⁻ ω, ENNReal.ofReal (min (σ 1 ω) M) ∂P ≤ ∫⁻ _, ENNReal.ofReal M ∂P :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (min_le_right _ _)
    _ < ⊤ := by simp

theorem nu_trunc_sup : ⨆ M : ℕ, nu P (fun n ω => min (σ n ω) M) = nu P σ := by
  unfold nu
  show ⨆ M : ℕ, ∫⁻ ω, ENNReal.ofReal (min (σ 1 ω) (M : ℝ)) ∂P = _
  have hm1 : Measurable (σ 1) := hσ.meas 0
  rw [← lintegral_iSup (f := fun M ω => ENNReal.ofReal (min (σ 1 ω) (M : ℝ)))
    (fun M => ENNReal.measurable_ofReal.comp (hm1.min measurable_const))]
  · congr 1
    funext ω
    apply le_antisymm (iSup_le fun M => ENNReal.ofReal_le_ofReal (min_le_left _ _))
    refine le_iSup_of_le ⌈σ 1 ω⌉₊ ?_
    rw [min_eq_left (Nat.le_ceil _)]
  · intro M M' h ω
    exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.2 h))

theorem Y_trunc_le (M k n : ℕ) (ω : Ω) : Y (fun n ω => min (σ n ω) M) k n ω ≤ Y σ k n ω := by
  unfold Y
  refine Finset.sum_le_sum fun j hj => Finset.prod_le_prod (fun i hi => ?_) (fun i _ => min_le_left _ _)
  rw [Finset.mem_Icc] at hj hi
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  exact le_min (hσ.nonneg i' ω) (Nat.cast_nonneg M)

theorem block_average_core (hk : 1 ≤ k) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ENNReal.ofReal (Y σ k n ω / n)) atTop (𝓝 (nu P σ ^ k)) := by
  rcases lt_or_eq_of_le (le_top : nu P σ ≤ ⊤) with hν | hν
  · exact block_avg_finite P σ hσ k hk hν
  · have hM := ae_all_iff.2 (fun M : ℕ => block_avg_finite P (fun n ω => min (σ n ω) M)
      (truncated_iid P σ hσ M) k hk (nu_trunc_lt_top P σ hσ M))
    filter_upwards [hM] with ω hω
    rw [hν, ENNReal.top_pow (by omega : k ≠ 0), ENNReal.tendsto_nhds_top_iff_nat]
    intro N
    have hsup := nu_trunc_sup P σ hσ
    rw [hν, iSup_eq_top] at hsup
    obtain ⟨M, hM'⟩ := hsup ((N : ENNReal) + 1) (by simp)
    have hNk : (N : ENNReal) < nu P (fun n ω => min (σ n ω) M) ^ k := by
      calc (N : ENNReal) < N + 1 := ENNReal.lt_add_right (ENNReal.natCast_ne_top N) one_ne_zero
        _ ≤ nu P (fun n ω => min (σ n ω) M) := hM'.le
        _ ≤ nu P (fun n ω => min (σ n ω) M) ^ k :=
          le_self_pow (le_trans (by simp) hM'.le) (by omega)
    filter_upwards [(hω M).eventually_const_lt hNk] with n hn
    calc (N : ENNReal) < ENNReal.ofReal (Y (fun n ω => min (σ n ω) M) k n ω / n) := hn
      _ ≤ ENNReal.ofReal (Y σ k n ω / n) :=
        ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (Y_trunc_le P σ hσ M k n ω)
          (Nat.cast_nonneg n))

end prob

theorem Z_eq_sum_core {Ω : Type*} (σ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Z σ n ω = ∑ j ∈ Finset.Icc 1 n, ∏ i ∈ Finset.Icc j n, σ i ω := by
  induction n with
  | zero => simp [Z]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp only [Z, ih, Finset.Icc_self, Finset.prod_singleton, Finset.mul_sum, mul_add, mul_one]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    rw [Finset.prod_Icc_succ_top (by omega), mul_comm]

theorem regroup_core {Ω : Type*} (σ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ∑ m ∈ Finset.Icc 1 n, Z σ m ω = ∑ k ∈ Finset.Icc 1 n, Y σ k n ω := by
  simp_rw [Z_eq_sum_core, Y]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => ⟨p.1 - p.2 + 1, p.2⟩) (fun p => ⟨p.2 + p.1 - 1, p.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp ⊢
    omega
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp ⊢
    omega
  · rintro ⟨m, j⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp
    simp only
    congr 1
    omega
  · rintro ⟨k, j⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp
    simp only
    congr 1
    omega
  · rintro ⟨m, j⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp
    simp only
    congr 2
    omega


theorem Y_nonneg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (σ : ℕ → Ω → ℝ)
    (hσ : IsIIDNonneg P σ) (k n : ℕ) (ω : Ω) : 0 ≤ Y σ k n ω := by
  rw [Y_eq_sum_W]
  exact Finset.sum_nonneg fun j _ => W_nonneg P σ hσ k j ω

theorem liminf_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (σ : ℕ → Ω → ℝ) (hσ : IsIIDNonneg P σ) :
    ∀ᵐ ω ∂P, ∑' k : ℕ, nu P σ ^ (k + 1) ≤
      liminf (fun n : ℕ => ENNReal.ofReal ((∑ m ∈ Finset.Icc 1 n, Z σ m ω) / n)) atTop := by
  have h := ae_all_iff.2 (fun k : ℕ => block_average_core P σ hσ (k + 1) (by omega))
  filter_upwards [h] with ω hω
  have hf : ∀ n, ENNReal.ofReal ((∑ m ∈ Finset.Icc 1 n, Z σ m ω) / n) =
      ∑ k ∈ Finset.range n, ENNReal.ofReal (Y σ (k + 1) n ω / n) := by
    intro n
    rw [regroup_core, Finset.sum_div, ENNReal.ofReal_sum_of_nonneg
      (fun k _ => div_nonneg (Y_nonneg P σ hσ k n ω) (Nat.cast_nonneg n))]
    refine Finset.sum_nbij' (fun k => k - 1) (fun k => k + 1) ?_ ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢; omega
    · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢; omega
    · intro j hj; simp only [Finset.mem_Icc, Finset.coe_Icc, Set.mem_Icc] at hj; omega
    · intro j hj; simp only [Finset.mem_range, Finset.coe_range, Set.mem_Iio] at hj; omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      congr 3
      omega
  simp_rw [hf]
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun K => ?_
  have hg : Tendsto (fun n => ∑ k ∈ Finset.range K, ENNReal.ofReal (Y σ (k + 1) n ω / n)) atTop
      (𝓝 (∑ k ∈ Finset.range K, nu P σ ^ (k + 1))) := tendsto_finset_sum _ fun k _ => hω k
  rw [← hg.liminf_eq]
  refine liminf_le_liminf ?_
  rw [eventually_atTop]
  exact ⟨K, fun n hn => Finset.sum_le_sum_of_subset (Finset.range_mono hn)⟩

end SolomonRWRE.DiffEq

open SolomonRWRE.DiffEq


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (σ : ℕ → Ω → ℝ) (hσ : IsIIDNonneg P σ) :
    ∀ᵐ ω ∂P, ∑' k : ℕ, nu P σ ^ (k + 1) ≤
      liminf (fun n : ℕ => ENNReal.ofReal ((∑ m ∈ Finset.Icc 1 n, Z σ m ω) / n)) atTop := by
  exact liminf_core P σ hσ
