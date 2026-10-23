-- Prove2me | solution 1 for RiskFunctionals.Conditional.continuity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T19:06:46.3622+00:00
-- url     : https://prove2.me/submissions/3c4c67f9-d596-40eb-afce-65b20bd9f9ab

import Mathlib
import Definitions.Def_RiskFunctionals_Conditional_Mappings
open RiskFunctionals.Conditional

open MeasureTheory

/-- Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 73,
Theorem 2.54: let `𝒜 : L_p(ℱ) → L_p(ℱ₁)` be a conditional acceptability mapping, `1 ≤ p < ∞`.
If `𝒜` is lower bounded on a neighborhood of some `Y₀`, i.e. there are a neighborhood `𝒰` of
zero and a bounded set `B ⊆ L_p(ℱ₁)` with `𝒜(Y) ∈ B + K` for all `Y ∈ Y₀ + 𝒰` (`K` the cone of
a.s. non-negative elements of `L_p(ℱ₁)`, so `𝒜(Y) ∈ B + K` means `b ≤ 𝒜(Y)` a.s. for some
`b ∈ B`), then `𝒜` is continuous on `L_p(ℱ)`. -/
theorem cc83_bound {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {p : ENNReal} [Fact (1 ≤ p)]
    (u d v : Lp ℝ p P) (hud : u ≤ d) (hdv : d ≤ v) : ‖d‖ ≤ ‖u‖ + ‖v‖ := by
  have h1 : |d| ≤ |u| + |v| := by
    apply sup_le
    · exact hdv.trans ((le_abs_self v).trans (le_add_of_nonneg_left (abs_nonneg u)))
    · exact (neg_le_neg hud).trans ((neg_le_abs u).trans (le_add_of_nonneg_right (abs_nonneg v)))
  have h2 : ‖d‖ ≤ ‖|u| + |v|‖ :=
    norm_le_norm_of_abs_le_abs (by rwa [abs_of_nonneg (add_nonneg (abs_nonneg u) (abs_nonneg v))])
  calc ‖d‖ ≤ ‖|u| + |v|‖ := h2
    _ ≤ ‖|u|‖ + ‖|v|‖ := norm_add_le _ _
    _ = ‖u‖ + ‖v‖ := by rw [norm_abs_eq_norm, norm_abs_eq_norm]

theorem solution {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (P : Measure[mΩ] Ω) [IsProbabilityMeasure P]
    (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (A : Lp ℝ p P → lpMeas ℝ ℝ m p P) (hA : IsConditionalAcceptabilityMapping A)
    (Y₀ : Lp ℝ p P) (U : Set (Lp ℝ p P)) (hU : U ∈ nhds (0 : Lp ℝ p P))
    (Bset : Set (Lp ℝ p P)) (hB_sub : Bset ⊆ lpMeas ℝ ℝ m p P)
    (hB_bdd : Bornology.IsBounded Bset)
    (hlow : ∀ Y ∈ U, ∃ b ∈ Bset, ∀ᵐ ω ∂P, b ω ≤ (A (Y₀ + Y) : Lp ℝ p P) ω) :
    Continuous (fun Y : Lp ℝ p P => (A Y : Lp ℝ p P)) := by
  set a : Lp ℝ p P → Lp ℝ p P := fun Y => (A Y : Lp ℝ p P) with ha
  have conc : ∀ (Y Y' : Lp ℝ p P) (t : ℝ), 0 ≤ t → t ≤ 1 →
      ∀ᵐ ω ∂P, t * a Y ω + (1 - t) * a Y' ω ≤ a (t • Y + (1 - t) • Y') ω :=
    fun Y Y' t h0 h1 => hA.concave Y Y' t h0 h1
  obtain ⟨r0, hr0, hball⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hB_bdd
  have lb : ∀ Y1 : Lp ℝ p P, ∃ C : ℝ, ∀ V : Lp ℝ p P, ‖V‖ < r0 / 2 →
      ∃ g : Lp ℝ p P, ‖g‖ ≤ C ∧ ∀ᵐ ω ∂P, g ω ≤ a (Y1 + V) ω := by
    intro Y1
    set Z := (2:ℝ) • Y1 - Y₀ with hZ
    refine ⟨(1/2) * M + (1/2) * ‖a Z‖, fun V hV => ?_⟩
    have hmem : (2:ℝ) • V ∈ U := hball (by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos two_pos]; linarith)
    obtain ⟨b, hbB, hb⟩ := hlow _ hmem
    refine ⟨(1/2:ℝ) • b + (1/2:ℝ) • a Z, ?_, ?_⟩
    · calc ‖(1/2:ℝ) • b + (1/2:ℝ) • a Z‖ ≤ ‖(1/2:ℝ) • b‖ + ‖(1/2:ℝ) • a Z‖ := norm_add_le _ _
        _ = (1/2) * ‖b‖ + (1/2) * ‖a Z‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
        _ ≤ (1/2) * M + (1/2) * ‖a Z‖ := by linarith [hM b hbB]
    · have hc := conc (Y₀ + (2:ℝ) • V) Z (1/2) (by norm_num) (by norm_num)
      have e : (1/2:ℝ) • (Y₀ + (2:ℝ) • V) + (1 - 1/2:ℝ) • Z = Y1 + V := by rw [hZ]; module
      rw [e] at hc
      filter_upwards [hc, hb, Lp.coeFn_add ((1/2:ℝ) • b) ((1/2:ℝ) • a Z), Lp.coeFn_smul (1/2:ℝ) b,
        Lp.coeFn_smul (1/2:ℝ) (a Z)] with ω h1 h2 h3 h4 h5
      rw [h3, Pi.add_apply, h4, h5]
      simp only [Pi.smul_apply, smul_eq_mul]
      linarith
  rw [Metric.continuous_iff]
  intro Y1 ε hε
  obtain ⟨C, hC⟩ := lb Y1
  set s := r0 / 4 with hs
  have hs0 : 0 < s := by positivity
  have core : ∀ W : Lp ℝ p P, 0 < ‖W‖ → ‖W‖ ≤ s →
      ‖a (Y1 + W) - a Y1‖ ≤ (‖W‖ / s) * (2 * C + 2 * ‖a Y1‖) := by
    intro W hW0 hWs
    set t := ‖W‖ / s with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hs0]; exact hWs
    set V := t⁻¹ • W with hV
    have hVn : ‖V‖ = s := by
      rw [hV, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ht0, ht]; field_simp
    have htV : t • V = W := by rw [hV, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
    obtain ⟨g1, hg1n, hg1⟩ := hC V (by rw [hVn]; linarith)
    obtain ⟨g2, hg2n, hg2⟩ := hC (-V) (by rw [norm_neg, hVn]; linarith)
    have c1 := conc (Y1 + V) Y1 t ht0.le ht1
    have e1 : t • (Y1 + V) + (1 - t) • Y1 = Y1 + W := by rw [smul_add, htV]; module
    rw [e1] at c1
    have c2 := conc (Y1 + -V) Y1 t ht0.le ht1
    have e2 : t • (Y1 + -V) + (1 - t) • Y1 = Y1 - W := by rw [smul_add, smul_neg, htV]; module
    rw [e2] at c2
    have c3 := conc (Y1 + W) (Y1 - W) (1/2) (by norm_num) (by norm_num)
    have e3 : (1/2:ℝ) • (Y1 + W) + (1 - 1/2:ℝ) • (Y1 - W) = Y1 := by module
    rw [e3] at c3
    have hud : t • (g1 - a Y1) ≤ a (Y1 + W) - a Y1 := by
      rw [← Lp.coeFn_le]
      filter_upwards [c1, hg1, Lp.coeFn_smul t (g1 - a Y1), Lp.coeFn_sub g1 (a Y1),
        Lp.coeFn_sub (a (Y1 + W)) (a Y1)] with ω h1 h2 h3 h4 h5
      rw [h3, h5, Pi.smul_apply, h4]
      simp only [Pi.sub_apply, smul_eq_mul]
      nlinarith
    have hdv : a (Y1 + W) - a Y1 ≤ t • (a Y1 - g2) := by
      rw [← Lp.coeFn_le]
      filter_upwards [c2, c3, hg2, Lp.coeFn_smul t (a Y1 - g2), Lp.coeFn_sub (a Y1) g2,
        Lp.coeFn_sub (a (Y1 + W)) (a Y1)] with ω h1 h3 h2 h4 h5 h6
      rw [h4, h6, Pi.smul_apply, h5]
      simp only [Pi.sub_apply, smul_eq_mul]
      nlinarith
    have hb := cc83_bound _ _ _ hud hdv
    rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at hb
    have n1 : ‖g1 - a Y1‖ ≤ C + ‖a Y1‖ := (norm_sub_le _ _).trans (by linarith)
    have n2 : ‖a Y1 - g2‖ ≤ ‖a Y1‖ + C := (norm_sub_le _ _).trans (by linarith)
    calc ‖a (Y1 + W) - a Y1‖ ≤ t * ‖g1 - a Y1‖ + t * ‖a Y1 - g2‖ := hb
      _ ≤ t * (C + ‖a Y1‖) + t * (‖a Y1‖ + C) := by gcongr
      _ = t * (2 * C + 2 * ‖a Y1‖) := by ring
  set K := |2 * C + 2 * ‖a Y1‖| + 1 with hK
  have hK0 : 0 < K := by positivity
  refine ⟨min s (ε * s / K), lt_min hs0 (by positivity), fun Y hY => ?_⟩
  rw [dist_eq_norm] at hY ⊢
  set W := Y - Y1 with hW
  have hYW : Y = Y1 + W := by rw [hW]; abel
  by_cases hW0 : ‖W‖ = 0
  · rw [norm_eq_zero] at hW0
    rw [hYW, hW0, add_zero, sub_self, norm_zero]; exact hε
  · have hWp : 0 < ‖W‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hW0)
    have h1 := core W hWp (hY.le.trans (min_le_left _ _))
    rw [hYW]
    have h2 : ‖W‖ < ε * s / K := hY.trans_le (min_le_right _ _)
    calc ‖a (Y1 + W) - a Y1‖ ≤ (‖W‖ / s) * (2 * C + 2 * ‖a Y1‖) := h1
      _ ≤ (‖W‖ / s) * K := by gcongr; rw [hK]; linarith [le_abs_self (2 * C + 2 * ‖a Y1‖)]
      _ < (ε * s / K / s) * K := by gcongr
      _ = ε := by field_simp



