-- Prove2me | solution 1 for PandemicInfo.Inequality.Ktil_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:50:29.669763+00:00
-- url     : https://prove2.me/submissions/0ebaba50-1c7f-4a92-8220-3769a31b2f2f

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_PandemicInfo_Inequality_Model
import Definitions.Def_PandemicInfo_Inequality_Reduced

namespace Aux_PI_Ktil

open MeasureTheory

lemma ae_ne_pt (x : ℝ) : ∀ᵐ c ∂(volume : Measure ℝ), c ≠ x := by
  rw [ae_iff]
  simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
  exact Real.volume_singleton

lemma split (f g1 g2 : ℝ → ℝ) (a x b : ℝ) (hax : a ≤ x) (hxb : x ≤ b)
    (hg1 : Continuous g1) (hg2 : Continuous g2)
    (h1 : ∀ c, a < c → c < x → f c = g1 c) (h2 : ∀ c, x < c → c < b → f c = g2 c) :
    ∫ c in a..b, f c = (∫ c in a..x, g1 c) + ∫ c in x..b, g2 c := by
  have ae1 : ∀ᵐ c ∂(volume : Measure ℝ), c ∈ Set.uIoc a x → f c = g1 c := by
    filter_upwards [ae_ne_pt x] with c hc hmem
    rw [Set.uIoc_of_le hax] at hmem
    exact h1 c hmem.1 (lt_of_le_of_ne hmem.2 hc)
  have ae2 : ∀ᵐ c ∂(volume : Measure ℝ), c ∈ Set.uIoc x b → f c = g2 c := by
    filter_upwards [ae_ne_pt b] with c hc hmem
    rw [Set.uIoc_of_le hxb] at hmem
    exact h2 c hmem.1 (lt_of_le_of_ne hmem.2 hc)
  have i1 : IntervalIntegrable f volume a x :=
    (intervalIntegrable_congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr ae1)).mpr
      (hg1.intervalIntegrable a x)
  have i2 : IntervalIntegrable f volume x b :=
    (intervalIntegrable_congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr ae2)).mpr
      (hg2.intervalIntegrable x b)
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2,
    intervalIntegral.integral_congr_ae ae1, intervalIntegral.integral_congr_ae ae2]

end Aux_PI_Ktil

open PandemicInfo.Inequality in
theorem solution (P : Params) (hS : P.Standing) (lam : ℝ) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1) (μ : ℝ) (hμ : μ ∈ Set.Icc P.ωl P.ωh) :
    P.Ktil lam μ =
      (3 * lam - 2) / (2 * P.γ) * (μ * P.κ * (P.θ + P.γ / 2) / (P.γ + μ * P.κ)) ^ 2 +
        (1 - lam) * (μ * P.κ * (P.θ + P.γ / 2) / (P.γ + μ * P.κ)) * (P.θ + P.γ / 2) / P.γ -
        lam * (P.θ - P.γ / 2) ^ 2 / (2 * P.γ) := by
  obtain ⟨hωl, _, _, _, _, hσ, hσθ, hκ, hcLo⟩ := hS
  have hs3 : 0 < Real.sqrt 3 := by positivity
  have hγpos : 0 < P.γ := by unfold Params.γ; positivity
  have hcLoE : P.cLo = P.θ - P.γ / 2 := by unfold Params.cLo Params.γ; ring
  have hcHiE : P.cHi = P.θ + P.γ / 2 := by unfold Params.cHi Params.γ; ring
  set x := μ * P.κ * (P.θ + P.γ / 2) / (P.γ + μ * P.κ) with hx
  have hxE : P.cStar μ = x := by unfold Params.cStar; rw [hx]; unfold Params.γ; ring
  have hμκ : P.ωl * P.κ ≤ μ * P.κ := mul_le_mul_of_nonneg_right hμ.1 hκ.le
  have hμpos : 0 < μ * P.κ := by nlinarith
  have hden : 0 < P.γ + μ * P.κ := by linarith
  have hb : 0 < P.θ + P.γ / 2 := by unfold Params.γ; nlinarith
  have hxb : x ≤ P.cHi := by
    rw [hcHiE, hx, div_le_iff₀ hden]; nlinarith
  have hax : P.cLo ≤ x := by
    rw [hx, le_div_iff₀ hden]
    have : P.cLo ≤ μ * P.κ := le_trans hcLo hμκ
    rw [hcLoE] at this ⊢
    nlinarith
  have hKe : (∫ c in P.cLo..P.cHi, if c ≤ x then c else 0) = (x ^ 2 - P.cLo ^ 2) / 2 := by
    rw [Aux_PI_Ktil.split _ (fun c => c) (fun _ => 0) _ _ _ hax hxb continuous_id
      continuous_const (fun c _ hc => if_pos hc.le) (fun c hc _ => if_neg (not_le.mpr hc))]
    simp [integral_id]
  have hKh : (∫ c in P.cLo..P.cHi, if x ≤ c then (1 : ℝ) else 0) = P.cHi - x := by
    rw [Aux_PI_Ktil.split _ (fun _ => 0) (fun _ => 1) _ _ _ hax hxb continuous_const
      continuous_const (fun c _ hc => if_neg (not_le.mpr hc)) (fun c hc _ => if_pos hc.le)]
    simp
  unfold Params.Ktil Params.Klam Params.Ke Params.Kh Params.Ec
  rw [hxE, hKe, hKh, hcLoE, hcHiE]
  field_simp
  ring
