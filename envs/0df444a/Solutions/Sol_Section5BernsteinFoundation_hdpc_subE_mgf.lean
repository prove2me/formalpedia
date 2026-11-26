-- Prove2me | solution 1 for Section5BernsteinFoundation.hdpc_subE_mgf
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:05:06.077464+00:00
-- url     : https://prove2.me/submissions/2259543a-2541-4ace-b3c0-fe767d31c01d

import Mathlib
section
/-! Reused fixed-scale Bernstein MGF argument by Nickrobbins95.
Prove2Me theorem ffb81651-cac7-4739-85c2-9cb4b69885be,
accepted submission 997bda66-5ba4-4af2-8457-558693e93561.
Only the fixed-scale argument is retained; no theorem placeholders are used. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace Section5BernsteinFoundation

lemma hdpc_exp_le_quad (y : ℝ) : exp y ≤ 1 + y + y ^ 2 * exp |y| := by
  rcases le_or_gt |y| 1 with hy | hy
  · have h1 := Real.abs_exp_sub_one_sub_id_le hy
    have h3 := (abs_le.1 h1).2
    have h4 : 1 ≤ exp |y| := Real.one_le_exp (abs_nonneg y)
    have h5 : y ^ 2 ≤ y ^ 2 * exp |y| := le_mul_of_one_le_right (sq_nonneg y) h4
    linarith
  · have hy2 : 1 ≤ y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
    have he : exp y ≤ exp |y| := exp_le_exp.2 (le_abs_self y)
    have h6 : exp |y| ≤ y ^ 2 * exp |y| := le_mul_of_one_le_left (exp_pos _).le hy2
    have h7 : |y| + 1 ≤ exp |y| := add_one_le_exp |y|
    rcases le_or_gt 0 y with h0 | h0
    · linarith
    · have h8 : exp y ≤ 1 := Real.exp_le_one_iff.2 h0.le
      have h9 : |y| = -y := abs_of_neg h0
      linarith

lemma hdpc_sq_le_exp (u : ℝ) (hu : 0 ≤ u) : u ^ 2 ≤ 16 * exp (u / 2) := by
  have h1 : u / 4 ≤ exp (u / 4) := by linarith [add_one_le_exp (u / 4)]
  have h2 : exp (u / 2) = exp (u / 4) * exp (u / 4) := by rw [← exp_add]; ring_nf
  have h3 : 0 ≤ u / 4 := by positivity
  have h4 := mul_le_mul h1 h1 h3 (exp_pos _).le
  nlinarith



end Section5BernsteinFoundation

end
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Real Filter Topology
namespace Section5BernsteinFoundation
end Section5BernsteinFoundation
open Section5BernsteinFoundation
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (hmean : ∫ ω, Y ω ∂P = 0) (s : ℝ) (hs : 0 < s)
    (hint : Integrable (fun ω => exp (|Y ω| / s)) P)
    (hle : ∫ ω, exp (|Y ω| / s) ∂P ≤ 2) (l : ℝ) (hl : |l| * s ≤ 1 / 2) :
    Integrable (fun ω => exp (l * Y ω)) P ∧ mgf Y P l ≤ exp (32 * l ^ 2 * s ^ 2) := by
  have hpt : ∀ ω, exp (l * Y ω) ≤ 1 + l * Y ω + 16 * l ^ 2 * s ^ 2 * exp (|Y ω| / s) ∧
      exp (l * Y ω) ≤ exp (|Y ω| / s) ∧ |Y ω| ≤ s * exp (|Y ω| / s) := by
    intro ω
    set u := |Y ω| / s with hu
    have hu0 : 0 ≤ u := div_nonneg (abs_nonneg _) hs.le
    have hYu : |Y ω| = s * u := by rw [hu]; field_simp
    have hsq : Y ω ^ 2 = s ^ 2 * u ^ 2 := by rw [← sq_abs, hYu]; ring
    have hlu : |l * Y ω| ≤ u / 2 := by
      rw [abs_mul, hYu]
      nlinarith [abs_nonneg l, mul_le_mul_of_nonneg_right hl hu0]
    have h1 := Section5BernsteinFoundation.hdpc_exp_le_quad (l * Y ω)
    have h2 : exp |l * Y ω| ≤ exp (u / 2) := exp_le_exp.2 hlu
    have h3 := Section5BernsteinFoundation.hdpc_sq_le_exp u hu0
    have h4 : exp u = exp (u / 2) * exp (u / 2) := by rw [← exp_add]; ring_nf
    have h5 : (l * Y ω) ^ 2 * exp |l * Y ω| ≤ 16 * l ^ 2 * s ^ 2 * exp u := by
      rw [mul_pow, hsq, h4]
      have hA : 0 ≤ l ^ 2 * s ^ 2 := by positivity
      calc l ^ 2 * (s ^ 2 * u ^ 2) * exp |l * Y ω|
          = (l ^ 2 * s ^ 2) * (u ^ 2 * exp |l * Y ω|) := by ring
        _ ≤ (l ^ 2 * s ^ 2) * ((16 * exp (u / 2)) * exp (u / 2)) := by
          apply mul_le_mul_of_nonneg_left _ hA
          exact mul_le_mul h3 h2 (exp_pos _).le (by positivity)
        _ = 16 * l ^ 2 * s ^ 2 * (exp (u / 2) * exp (u / 2)) := by ring
    refine ⟨by linarith, ?_, ?_⟩
    · apply exp_le_exp.2
      have := le_abs_self (l * Y ω)
      linarith
    · rw [hYu]
      have := add_one_le_exp u
      nlinarith
  have hintE : Integrable (fun ω => exp (l * Y ω)) P := by
    refine Integrable.mono' hint ((hY.const_mul l).exp.aestronglyMeasurable)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact (hpt ω).2.1
  have hYint : Integrable Y P := by
    refine Integrable.mono' (hint.const_mul s) hY.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact (hpt ω).2.2
  refine ⟨hintE, ?_⟩
  have hI1 : Integrable (fun ω => 1 + l * Y ω) P := (integrable_const _).add (hYint.const_mul l)
  have hI2 : Integrable (fun ω => 16 * l ^ 2 * s ^ 2 * exp (|Y ω| / s)) P := hint.const_mul _
  rw [mgf]
  calc ∫ ω, exp (l * Y ω) ∂P
      ≤ ∫ ω, (1 + l * Y ω + 16 * l ^ 2 * s ^ 2 * exp (|Y ω| / s)) ∂P :=
        integral_mono hintE (hI1.add hI2) (fun ω => (hpt ω).1)
    _ = 1 + l * ∫ ω, Y ω ∂P + 16 * l ^ 2 * s ^ 2 * ∫ ω, exp (|Y ω| / s) ∂P := by
        rw [integral_add hI1 hI2, integral_add (integrable_const _) (hYint.const_mul l),
          integral_const_mul, integral_const_mul, integral_const]
        simp
    _ ≤ 1 + 32 * l ^ 2 * s ^ 2 := by
        rw [hmean]
        have hq0 : 0 ≤ 16 * l ^ 2 * s ^ 2 := by positivity
        nlinarith
    _ ≤ exp (32 * l ^ 2 * s ^ 2) := by linarith [add_one_le_exp (32 * l ^ 2 * s ^ 2)]
