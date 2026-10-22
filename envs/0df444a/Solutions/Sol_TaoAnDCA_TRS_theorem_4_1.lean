-- Prove2me | solution 1 for TaoAnDCA.TRS.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T14:41:02.384902+00:00
-- url     : https://prove2.me/submissions/74710f89-c880-4d37-ad23-a4fc01d91d27

import Mathlib
import Definitions.Def_TaoAnDCA_TRS_Setting

set_option autoImplicit false

open Filter Topology

namespace TRS382b

open TaoAnDCA.TRS

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

lemma step_norm_le {n : ℕ} (A : E n →L[ℝ] E n) (b : E n) (r ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ)
    (z : E n) : ‖dcaStep A b ρ r z‖ ≤ r := by
  unfold dcaStep
  split_ifs with h
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [one_div, inv_mul_le_iff₀ hρ]
    linarith
  · have hw : 0 < ‖ρ • z - A z - b‖ := by
      have : ρ * r < ‖ρ • z - A z - b‖ := lt_of_not_ge h
      have : 0 < ρ * r := mul_pos hρ hr
      linarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), div_mul_cancel₀ _ hw.ne']

lemma step_eq {n : ℕ} (A : E n →L[ℝ] E n) (b : E n) (r ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ)
    (z : E n) : dcaStep A b ρ r z =
      (r / max (ρ * r) ‖ρ • z - A z - b‖) • (ρ • z - A z - b) := by
  unfold dcaStep
  split_ifs with h
  · rw [max_eq_left h]
    congr 1
    field_simp
  · rw [max_eq_right (le_of_lt (lt_of_not_ge h))]

lemma step_cont {n : ℕ} (A : E n →L[ℝ] E n) (b : E n) (r ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ) :
    Continuous (dcaStep A b ρ r) := by
  have heq : dcaStep A b ρ r =
      fun z => (r / max (ρ * r) ‖ρ • z - A z - b‖) • (ρ • z - A z - b) := by
    funext z; exact step_eq A b r ρ hr hρ z
  rw [heq]
  have hw : Continuous (fun z : E n => ρ • z - A z - b) := by fun_prop
  have hc : Continuous (fun z : E n => r / max (ρ * r) ‖ρ • z - A z - b‖) := by
    refine continuous_const.div (continuous_const.max hw.norm) ?_
    intro z
    have : 0 < ρ * r := mul_pos hρ hr
    exact ne_of_gt (lt_of_lt_of_le this (le_max_left _ _))
  exact hc.smul hw

lemma proj_ineq {n : ℕ} (A : E n →L[ℝ] E n) (b : E n) (r ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ)
    (z : E n) (hz : ‖z‖ ≤ r) :
    inner ℝ (dcaStep A b ρ r z - z) (ρ • dcaStep A b ρ r z - (ρ • z - A z - b)) ≤ 0 := by
  unfold dcaStep
  split_ifs with h
  · rw [smul_smul, mul_one_div_cancel hρ.ne', one_smul, sub_self, inner_zero_right]
  · set w := ρ • z - A z - b with hwdef
    have hlt : ρ * r < ‖w‖ := lt_of_not_ge h
    have hw : 0 < ‖w‖ := lt_trans (mul_pos hρ hr) hlt
    have e1 : ρ • ((r / ‖w‖) • w) - w = (ρ * r / ‖w‖ - 1) • w := by
      rw [smul_smul, sub_smul, one_smul, mul_div_assoc]
    rw [e1, inner_smul_right, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [conj_trivial]
    have hzw : inner ℝ z w ≤ r * ‖w‖ := by
      have := real_inner_le_norm z w
      nlinarith [norm_nonneg w]
    have hc : ρ * r / ‖w‖ - 1 < 0 := by
      rw [sub_neg, div_lt_one hw]; exact hlt
    have h2 : r / ‖w‖ * ‖w‖ ^ 2 = r * ‖w‖ := by field_simp
    rw [h2]
    have : 0 ≤ r * ‖w‖ - inner ℝ z w := by linarith
    nlinarith

lemma descent {n : ℕ} (A : E n →L[ℝ] E n) (hA : IsSelfAdjoint A) (b : E n) (r ρ : ℝ)
    (hr : 0 < r) (hρ : 0 < ρ) (μ : ℝ)
    (hμ : ∀ z : E n, μ * ‖z‖ ^ 2 ≤ inner ℝ z (ρ • z - A z))
    (z : E n) (hz : ‖z‖ ≤ r) :
    quad A b (dcaStep A b ρ r z) ≤
      quad A b z - (ρ + μ) / 2 * ‖dcaStep A b ρ r z - z‖ ^ 2 := by
  have key := proj_ineq A b r ρ hr hρ z hz
  set z' := dcaStep A b ρ r z
  set d := z' - z with hd
  have hz' : z' = z + d := by rw [hd]; abel
  have hsym : ∀ u v : E n, inner ℝ (A u) v = inner ℝ u (A v) := by
    intro u v
    exact hA.isSymmetric u v
  have hμd := hμ d
  have e1 : quad A b z' - quad A b z =
      inner ℝ d (A z) + 1 / 2 * inner ℝ d (A d) + inner ℝ b d := by
    unfold quad
    rw [hz', map_add, inner_add_left, inner_add_right, inner_add_right, inner_add_right]
    have : inner ℝ z (A d) = inner ℝ d (A z) := by
      rw [← hsym, real_inner_comm]
    rw [this]
    ring
  have e2 : inner ℝ d (ρ • z' - (ρ • z - A z - b)) =
      inner ℝ d (A z) + inner ℝ b d + ρ * ‖d‖ ^ 2 := by
    have : ρ • z' - (ρ • z - A z - b) = ρ • d + A z + b := by
      rw [hz', smul_add]; abel
    rw [this, inner_add_right, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
      real_inner_comm b d]
    ring
  have e3 : inner ℝ d (ρ • d - A d) = ρ * ‖d‖ ^ 2 - inner ℝ d (A d) := by
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
  rw [e3] at hμd
  rw [e2] at key
  linarith

lemma quad_lb {n : ℕ} (A : E n →L[ℝ] E n) (b : E n) (r : ℝ) (y : E n) (hy : ‖y‖ ≤ r) :
    -(1 / 2 * (‖A‖ * r ^ 2) + ‖b‖ * r) ≤ quad A b y := by
  unfold quad
  have h1 : -(‖y‖ * ‖A y‖) ≤ inner ℝ y (A y) := by
    have := abs_real_inner_le_norm y (A y)
    linarith [neg_abs_le (inner ℝ y (A y))]
  have h2 : ‖A y‖ ≤ ‖A‖ * ‖y‖ := A.le_opNorm y
  have h3 : -(‖b‖ * ‖y‖) ≤ inner ℝ b y := by
    have := abs_real_inner_le_norm b y
    linarith [neg_abs_le (inner ℝ b y)]
  have hy0 := norm_nonneg y
  have hA0 := norm_nonneg A
  have hb0 := norm_nonneg b
  have h4 : ‖y‖ * ‖A y‖ ≤ ‖A‖ * r ^ 2 := by
    calc ‖y‖ * ‖A y‖ ≤ ‖y‖ * (‖A‖ * ‖y‖) := mul_le_mul_of_nonneg_left h2 hy0
      _ = ‖A‖ * (‖y‖ * ‖y‖) := by ring
      _ ≤ ‖A‖ * (r * r) := by
          apply mul_le_mul_of_nonneg_left _ hA0
          exact mul_le_mul hy hy hy0 (le_trans hy0 hy)
      _ = ‖A‖ * r ^ 2 := by ring
  have h5 : ‖b‖ * ‖y‖ ≤ ‖b‖ * r := mul_le_mul_of_nonneg_left hy hb0
  linarith

lemma kkt_of_fixed {n : ℕ} (A : E n →L[ℝ] E n) (b : E n) (r ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ)
    (z : E n) (hfix : dcaStep A b ρ r z = z) : ∃ lam : ℝ, IsKKT A b r z lam := by
  rw [step_eq A b r ρ hr hρ] at hfix
  set w := ρ • z - A z - b with hwdef
  set M := max (ρ * r) ‖w‖ with hMdef
  have hρr : 0 < ρ * r := mul_pos hρ hr
  have hM : 0 < M := lt_of_lt_of_le hρr (le_max_left _ _)
  have hMw : ‖w‖ ≤ M := le_max_right _ _
  have hMr : ρ * r ≤ M := le_max_left _ _
  refine ⟨M / r - ρ, ?_, ?_, ?_, ?_⟩
  · rw [sub_nonneg, le_div_iff₀ hr]; exact hMr
  · have h1 : (M / r) • z = w := by
      calc (M / r) • z = (M / r) • ((r / M) • w) := by rw [hfix]
        _ = w := by
          rw [smul_smul]
          have : M / r * (r / M) = 1 := by field_simp
          rw [this, one_smul]
    rw [sub_smul, h1, hwdef]
    abel
  · rcases le_total ‖w‖ (ρ * r) with h | h
    · have : M = ρ * r := max_eq_left h
      rw [this]
      have : ρ * r / r - ρ = 0 := by field_simp; ring
      rw [this, zero_mul]
    · have hM' : M = ‖w‖ := max_eq_right h
      have hw0 : 0 < ‖w‖ := lt_of_lt_of_le hρr h
      have : ‖z‖ = r := by
        rw [← hfix, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hM), hM',
          div_mul_cancel₀ _ hw0.ne']
      rw [this, sub_self, mul_zero]
  · rw [← hfix, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hM)]
    calc r / M * ‖w‖ ≤ r / M * M := mul_le_mul_of_nonneg_left hMw (div_pos hr hM).le
      _ = r := div_mul_cancel₀ _ hM.ne'

end TRS382b

open Filter Topology TaoAnDCA.TRS in
theorem solution {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) (ρ : ℝ) (hρ : 0 < ρ)
    (hρA : ∀ z : EuclideanSpace ℝ (Fin n), 0 ≤ inner ℝ z (ρ • z - A z))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsTRSDCARun A b ρ r x) :
    (∀ μ : ℝ, (∀ z : EuclideanSpace ℝ (Fin n), μ * ‖z‖ ^ 2 ≤ inner ℝ z (ρ • z - A z)) →
      ∀ k : ℕ, trsObj A b r (x (k + 1)) ≤
        trsObj A b r (x k) - (((ρ + μ) / 2 * ‖x (k + 1) - x k‖ ^ 2 : ℝ) : EReal)) ∧
    (Antitone (fun k => trsObj A b r (x k)) ∧
      ∃ α' : EReal, Tendsto (fun k => trsObj A b r (x k)) atTop (𝓝 α') ∧ trsValue A b r ≤ α') ∧
    Tendsto (fun k => ‖x (k + 1) - x k‖) atTop (𝓝 0) ∧
    (∀ xs : EuclideanSpace ℝ (Fin n), MapClusterPt xs atTop x → ∃ lam : ℝ, IsKKT A b r xs lam) := by
  have h0 : ∀ z : EuclideanSpace ℝ (Fin n), (0 : ℝ) * ‖z‖ ^ 2 ≤ inner ℝ z (ρ • z - A z) := by
    intro z; rw [zero_mul]; exact hρA z
  have hball : ∀ k, ‖x (k + 1)‖ ≤ r := by
    intro k; rw [hx k]; exact TRS382b.step_norm_le A b r ρ hr hρ (x k)
  have item1 : ∀ μ : ℝ, (∀ z : EuclideanSpace ℝ (Fin n), μ * ‖z‖ ^ 2 ≤ inner ℝ z (ρ • z - A z)) →
      ∀ k : ℕ, trsObj A b r (x (k + 1)) ≤
        trsObj A b r (x k) - (((ρ + μ) / 2 * ‖x (k + 1) - x k‖ ^ 2 : ℝ) : EReal) := by
    intro μ hμ k
    by_cases h : ‖x k‖ ≤ r
    · have hd := TRS382b.descent A hA b r ρ hr hρ μ hμ (x k) h
      rw [← hx k] at hd
      unfold trsObj
      rw [if_pos (hball k), if_pos h, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      exact hd
    · conv_rhs => rw [trsObj, if_neg h]
      rw [EReal.top_sub_coe]
      exact le_top
  have hstep : ∀ k, trsObj A b r (x (k + 1)) ≤ trsObj A b r (x k) := by
    intro k
    by_cases h : ‖x k‖ ≤ r
    · have hd := TRS382b.descent A hA b r ρ hr hρ 0 h0 (x k) h
      rw [← hx k] at hd
      unfold trsObj
      rw [if_pos (hball k), if_pos h, EReal.coe_le_coe_iff]
      have : 0 ≤ (ρ + 0) / 2 * ‖x (k + 1) - x k‖ ^ 2 := by positivity
      linarith
    · conv_rhs => rw [trsObj, if_neg h]
      exact le_top
  have hanti : Antitone (fun k => trsObj A b r (x k)) := antitone_nat_of_succ_le hstep
  -- item 3
  have item3 : Tendsto (fun k => ‖x (k + 1) - x k‖) atTop (𝓝 0) := by
    set s : ℕ → ℝ := fun k => quad A b (x (k + 1)) with hs
    have hdesc : ∀ k, s (k + 1) ≤ s k - (ρ + 0) / 2 * ‖x (k + 1 + 1) - x (k + 1)‖ ^ 2 := by
      intro k
      have hd := TRS382b.descent A hA b r ρ hr hρ 0 h0 (x (k + 1)) (hball k)
      rw [← hx (k + 1)] at hd
      exact hd
    have santi : Antitone s := by
      apply antitone_nat_of_succ_le
      intro k
      have := hdesc k
      have : 0 ≤ (ρ + 0) / 2 * ‖x (k + 1 + 1) - x (k + 1)‖ ^ 2 := by positivity
      linarith
    have sbdd : BddBelow (Set.range s) := by
      refine ⟨-(1 / 2 * (‖A‖ * r ^ 2) + ‖b‖ * r), ?_⟩
      rintro _ ⟨k, rfl⟩
      exact TRS382b.quad_lb A b r _ (hball k)
    have hconv := tendsto_atTop_ciInf santi sbdd
    have hdiff : Tendsto (fun k => s k - s (k + 1)) atTop (𝓝 0) := by
      have := hconv.sub (hconv.comp (tendsto_add_atTop_nat 1))
      rw [sub_self] at this
      exact this
    have hsq : Tendsto (fun k => ‖x (k + 1 + 1) - x (k + 1)‖ ^ 2) atTop (𝓝 0) := by
      have hup : Tendsto (fun k => 2 / ρ * (s k - s (k + 1))) atTop (𝓝 0) := by
        have := hdiff.const_mul (2 / ρ)
        rw [mul_zero] at this
        exact this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup ?_ ?_
      · intro k; positivity
      · intro k
        have := hdesc k
        have h2 : ‖x (k + 1 + 1) - x (k + 1)‖ ^ 2 * ρ ≤ 2 * (s k - s (k + 1)) := by linarith
        calc ‖x (k + 1 + 1) - x (k + 1)‖ ^ 2
            = (‖x (k + 1 + 1) - x (k + 1)‖ ^ 2 * ρ) / ρ := by field_simp
          _ ≤ (2 * (s k - s (k + 1))) / ρ := by gcongr
          _ = 2 / ρ * (s k - s (k + 1)) := by ring
    have hn : Tendsto (fun k => ‖x (k + 1 + 1) - x (k + 1)‖) atTop (𝓝 0) := by
      have := hsq.sqrt
      rw [Real.sqrt_zero] at this
      refine this.congr ?_
      intro k
      exact Real.sqrt_sq (norm_nonneg _)
    exact (Filter.tendsto_add_atTop_iff_nat 1).mp hn
  refine ⟨item1, ⟨hanti, ⨅ k, trsObj A b r (x k), tendsto_atTop_iInf hanti, ?_⟩, item3, ?_⟩
  · exact le_iInf (fun k => iInf_le _ _)
  · intro xs hxs
    obtain ⟨ψ, hψ, hlim⟩ := MapClusterPt.tendsto_subseq hxs
    have hd : Tendsto (fun k => x (ψ k + 1) - x (ψ k)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      exact item3.comp hψ.tendsto_atTop
    have h1 : Tendsto (fun k => x (ψ k + 1)) atTop (𝓝 xs) := by
      have := hlim.add hd
      rw [add_zero] at this
      refine this.congr ?_
      intro k
      simp
    have h2 : Tendsto (fun k => x (ψ k + 1)) atTop (𝓝 (dcaStep A b ρ r xs)) := by
      have := ((TRS382b.step_cont A b r ρ hr hρ).tendsto xs).comp hlim
      refine this.congr ?_
      intro k
      simp [Function.comp, hx (ψ k)]
    have hfix : dcaStep A b ρ r xs = xs := tendsto_nhds_unique h2 h1
    exact TRS382b.kkt_of_fixed A b r ρ hr hρ xs hfix
