-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P21.restrictedCandidateDescent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T10:33:11.498807+00:00
-- url     : https://prove2.me/submissions/03d18eb4-e7d7-4bff-8b93-f7cd0c01f7e9

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

theorem x8_xs_pt (a b c d w z : ℝ) : pt (xstate a b c d w z) = xstate a b c d z w := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> simp [pt, xstate]

theorem x8_xs_add (a b c d w z a' b' c' d' w' z' : ℝ) :
    xstate a b c d w z + xstate a' b' c' d' w' z' =
      xstate (a + a') (b + b') (c + c') (d + d') (w + w') (z + z') := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> simp [xstate]

theorem x8_xs_smul (r a b c d w z : ℝ) :
    (r : ℂ) • xstate a b c d w z = xstate (r * a) (r * b) (r * c) (r * d) (r * w) (r * z) := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> simp [xstate]

theorem x8_xs_trace (a b c d w z : ℝ) :
    (xstate a b c d w z).trace = ((a + b + c + d : ℝ) : ℂ) := by
  simp [Matrix.trace, xstate, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

theorem x8_noiseEx : noiseEx = xstate 0 (1/20) (1/5) 0 0 0 := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [noiseEx, compressed, xstate, proj, QAlgorithms.pureDensity, QAlgorithms.ket]

theorem x8_noiseOld : noiseOld = xstate (3/40) (3/20) (3/80) (3/40) (-3/40) (3/40) := by
  have h2 : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1/2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [noiseOld, xstate, proj, QAlgorithms.pureDensity, QAlgorithms.ket, h2] <;> (try ring_nf) <;>
    (try simp [map_ofNat]) <;> (try norm_num)

theorem x8_quad2 {a d w X Y : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (h : w ^ 2 ≤ a * d) :
    0 ≤ a * X ^ 2 + 2 * w * X * Y + d * Y ^ 2 := by
  rcases ha.eq_or_lt with h0 | h0
  · subst h0
    have : w = 0 := by nlinarith [sq_nonneg w]
    subst this; nlinarith [sq_nonneg Y]
  · have : 0 ≤ a * (a * X ^ 2 + 2 * w * X * Y + d * Y ^ 2) := by
      nlinarith [sq_nonneg (a * X + w * Y), sq_nonneg Y]
    exact (mul_nonneg_iff_of_pos_left h0).1 this

theorem x8_xs_psd {a b c d w z : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hw : w ^ 2 ≤ a * d) (hz : z ^ 2 ≤ b * c) : (xstate a b c d w z).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext ⟨i1, i2⟩ ⟨j1, j2⟩
    fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
      simp [xstate, Matrix.conjTranspose_apply]
  · simp [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two, xstate]
    rw [Complex.le_def]
    simp
    refine ⟨?_, by ring⟩
    have h1 := x8_quad2 (X := (x (0, 0)).re) (Y := (x (1, 1)).re) ha hd hw
    have h2 := x8_quad2 (X := (x (0, 0)).im) (Y := (x (1, 1)).im) ha hd hw
    have h3 := x8_quad2 (X := (x (0, 1)).re) (Y := (x (1, 0)).re) hb hc hz
    have h4 := x8_quad2 (X := (x (0, 1)).im) (Y := (x (1, 0)).im) hb hc hz
    nlinarith [h1, h2, h3, h4]

theorem x8_descent (t : ℝ) : descent t = xstate (3/40*(1-t)) (3/20*(1-t) + t/20)
    (3/80*(1-t) + t/5) (3/40*(1-t)) (-3/40*(1-t)) (3/40*(1-t)) := by
  unfold descent
  rw [x8_noiseOld, x8_noiseEx]
  have : (1 - t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; ring
  rw [this, x8_xs_smul, x8_xs_smul, x8_xs_add]
  congr 1 <;> ring

theorem x8_tau (t : ℝ) : (descent t).trace.re = 27/80 - 7*t/80 := by
  rw [x8_descent, x8_xs_trace, Complex.ofReal_re]; ring

theorem x8_main :
  (∀ t : ℝ, 0≤t → t≤1 → primalS rhoEx (descent t) ∧
    (descent t).trace.re=27/80-7*t/80 ∧ (0<t → (descent t).trace.re<noiseOld.trace.re)) ∧
  ContinuousAt (fun t : ℝ => (((descent t).trace.re)⁻¹:ℂ) • descent t) 0 ∧
  ContinuousAt (fun t : ℝ => ((1+(descent t).trace.re)⁻¹:ℂ) • (rhoEx+descent t)) 0 := by
  have hold : noiseOld.trace.re = 27/80 := by
    rw [x8_noiseOld, x8_xs_trace, Complex.ofReal_re]; norm_num
  have hd : Continuous descent := by unfold descent; fun_prop
  refine ⟨fun t h0 h1 => ⟨⟨⟨?_, ?_⟩, ?_⟩, x8_tau t, fun ht => ?_⟩, ?_, ?_⟩
  · rw [x8_descent]
    apply x8_xs_psd <;> nlinarith
  · rw [x8_descent, x8_xs_pt, show rhoEx = xstate (3/8) (1/5) (1/20) (3/8) (1/4) (1/100) from rfl,
      x8_xs_pt, x8_xs_add]
    apply x8_xs_psd <;> nlinarith [mul_nonneg h0 (sub_nonneg.2 h1)]
  · rw [x8_descent, x8_xs_pt]
    apply x8_xs_psd <;> nlinarith
  · rw [x8_tau, hold]; linarith
  · simp only [x8_tau]
    have hs : ContinuousAt (fun t : ℝ => ((↑(27/80 - 7*t/80 : ℝ) : ℂ))⁻¹) 0 := by
      apply ContinuousAt.inv₀ (by fun_prop)
      push_cast; norm_num
    exact hs.smul hd.continuousAt
  · simp only [x8_tau]
    have hs : ContinuousAt (fun t : ℝ => (1 + (↑(27/80 - 7*t/80 : ℝ) : ℂ))⁻¹) 0 := by
      apply ContinuousAt.inv₀ (by fun_prop)
      push_cast; norm_num
    exact hs.smul (continuous_const.add hd).continuousAt

end QAlgorithms.Papers.Independent.Information100.P21

open QAlgorithms.Papers.Independent.Information100.P21 in
theorem solution :
  (∀ t : ℝ, 0≤t → t≤1 → primalS rhoEx (descent t) ∧
    (descent t).trace.re=27/80-7*t/80 ∧ (0<t → (descent t).trace.re<noiseOld.trace.re)) ∧
  ContinuousAt (fun t : ℝ => (((descent t).trace.re)⁻¹:ℂ) • descent t) 0 ∧
  ContinuousAt (fun t : ℝ => ((1+(descent t).trace.re)⁻¹:ℂ) • (rhoEx+descent t)) 0 := x8_main
