-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P56.diagonal_second_derivative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T06:12:01.746091+00:00
-- url     : https://prove2.me/submissions/b2938233-f558-45a3-829d-ce1cd7bb85e1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

open QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

lemma h54e_g {s : ℝ} (hs : |s| < 1) :
    HasDerivAt (fun s : ℝ => Real.binEntropy ((1 + s) / 2)) (-inverseTanh s) s := by
  have h1 := abs_lt.mp hs
  have hin : HasDerivAt (fun s : ℝ => (1 + s) / 2) (1/2) s := by
    simpa using ((hasDerivAt_id s).const_add 1).div_const 2
  have hb := Real.hasDerivAt_binEntropy (p := (1 + s) / 2) (by linarith) (by linarith)
  have := hb.comp s hin
  have e : (Real.log (1 - (1 + s) / 2) - Real.log ((1 + s) / 2)) * (1 / 2) = -inverseTanh s := by
    unfold inverseTanh
    have e1 : 1 - (1 + s) / 2 = (1 - s) / 2 := by ring
    rw [e1, Real.log_div (by linarith) (by norm_num), Real.log_div (by linarith) (by norm_num)]
    ring
  rw [e] at this
  exact this

lemma h54e_atanh {s : ℝ} (hs : |s| < 1) :
    HasDerivAt inverseTanh (1 / (1 - s ^ 2)) s := by
  have h1 := abs_lt.mp hs
  have ha : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + s)) s := by
    have := ((hasDerivAt_id s).const_add 1).log (by simp; linarith)
    simpa using this
  have hb : HasDerivAt (fun s : ℝ => Real.log (1 - s)) (-1 / (1 - s)) s := by
    have := ((hasDerivAt_id s).const_sub 1).log (by simp; linarith)
    simpa [neg_div] using this
  have := (ha.sub hb).div_const 2
  have e : (1 / (1 + s) - -1 / (1 - s)) / 2 = 1 / (1 - s ^ 2) := by
    have : (1 + s) ≠ 0 := by linarith
    have : (1 - s) ≠ 0 := by linarith
    have : (1 - s^2) ≠ 0 := by nlinarith
    field_simp
    ring
  rw [e] at this
  exact this

lemma h54e_R {u k z : ℝ} (hu : 0 < u) (hk : 0 ≤ k) :
    HasDerivAt (fun z : ℝ => Real.sqrt (u + k * z ^ 2)) (k * z / Real.sqrt (u + k * z ^ 2)) z := by
  have hpos : 0 < u + k * z ^ 2 := by positivity
  have hf : HasDerivAt (fun z : ℝ => u + k * z ^ 2) (k * (2 * z)) z := by
    have := ((hasDerivAt_pow 2 z).const_mul k).const_add u
    simpa using this
  have := hf.sqrt hpos.ne'
  have hs : Real.sqrt (u + k * z ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have e : k * (2 * z) / (2 * Real.sqrt (u + k * z ^ 2)) = k * z / Real.sqrt (u + k * z ^ 2) := by
    field_simp
  rw [e] at this
  exact this

lemma h54e_dom {p z : ℝ} (hp : 0 < p ∧ p < 1 / 2) (hz : |z| < 1) :
    0 < (1 - 2 * p) ^ 2 ∧ 0 < 1 - (1 - 2 * p) ^ 2 ∧ |(1 - 2 * p) * z| < 1 ∧
    0 < Real.sqrt ((1 - 2 * p) ^ 2 + (1 - (1 - 2 * p) ^ 2) * z ^ 2) ∧
    |Real.sqrt ((1 - 2 * p) ^ 2 + (1 - (1 - 2 * p) ^ 2) * z ^ 2)| < 1 := by
  obtain ⟨h0, h1⟩ := hp
  have hz2 : z ^ 2 < 1 := by
    have := abs_lt.mp hz; nlinarith
  have hz0 : 0 ≤ z ^ 2 := sq_nonneg z
  have ha0 : 0 < 1 - 2 * p := by linarith
  have ha1 : 1 - 2 * p < 1 := by linarith
  have hu : 0 < (1 - 2 * p) ^ 2 := by positivity
  have hu1 : (1 - 2 * p) ^ 2 < 1 := by nlinarith
  have hk : 0 < 1 - (1 - 2 * p) ^ 2 := by linarith
  refine ⟨hu, hk, ?_, ?_, ?_⟩
  · rw [abs_mul, abs_of_pos ha0]
    have := abs_nonneg z
    nlinarith
  · apply Real.sqrt_pos.mpr; positivity
  · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [Real.sqrt_lt' (by norm_num)]
    nlinarith

def h54e_F1 (p z : ℝ) : ℝ :=
  -(1 - 2 * p) * inverseTanh ((1 - 2 * p) * z) +
    (1 - (1 - 2 * p) ^ 2) * z *
      inverseTanh (Real.sqrt ((1 - 2 * p) ^ 2 + (1 - (1 - 2 * p) ^ 2) * z ^ 2)) /
      Real.sqrt ((1 - 2 * p) ^ 2 + (1 - (1 - 2 * p) ^ 2) * z ^ 2)

lemma h54e_d1 {p z : ℝ} (hp : 0 < p ∧ p < 1 / 2) (hz : |z| < 1) :
    HasDerivAt (diagonalDelta p) (h54e_F1 p z) z := by
  obtain ⟨hu, hk, haz, hr0, hr1⟩ := h54e_dom hp hz
  set a := 1 - 2 * p
  set u := a ^ 2
  set k := 1 - u
  have hfun : diagonalDelta p = fun z => (fun s : ℝ => Real.binEntropy ((1 + s) / 2)) (a * z) -
      (fun s : ℝ => Real.binEntropy ((1 + s) / 2)) (Real.sqrt (u + k * z ^ 2)) := by
    funext z; rfl
  rw [hfun]
  have hA : HasDerivAt (fun z : ℝ => a * z) a z := by
    simpa using (hasDerivAt_id z).const_mul a
  have h1 := (h54e_g haz).comp z hA
  have h2 := (h54e_g hr1).comp z (h54e_R (z := z) hu hk.le)
  have := h1.sub h2
  have e : -inverseTanh (a * z) * a - -inverseTanh (Real.sqrt (u + k * z ^ 2)) *
      (k * z / Real.sqrt (u + k * z ^ 2)) = h54e_F1 p z := by
    unfold h54e_F1; ring
  rw [e] at this
  exact this

lemma h54e_alg (a k z r T : ℝ) (hr : r ≠ 0) (h1r : 1 - r ^ 2 ≠ 0) (haz : 1 - (a * z) ^ 2 ≠ 0)
    (hrr : r ^ 2 = a ^ 2 + k * z ^ 2) :
    -a * (1 / (1 - (a * z) ^ 2) * a) +
      ((k * T + k * z * (1 / (1 - r ^ 2) * (k * z / r))) * r - k * z * T * (k * z / r)) / r ^ 2 =
    -a ^ 2 / (1 - a ^ 2 * z ^ 2) + k * a ^ 2 * T / r ^ 3 + k ^ 2 * z ^ 2 / (r ^ 2 * (1 - r ^ 2)) := by
  have e1 : -a * (1 / (1 - (a * z) ^ 2) * a) +
      ((k * T + k * z * (1 / (1 - r ^ 2) * (k * z / r))) * r - k * z * T * (k * z / r)) / r ^ 2 =
      -a ^ 2 / (1 - a ^ 2 * z ^ 2) + k * (r ^ 2 - k * z ^ 2) * T / r ^ 3 +
        k ^ 2 * z ^ 2 / (r ^ 2 * (1 - r ^ 2)) := by
    have : 1 - a ^ 2 * z ^ 2 ≠ 0 := by rw [← mul_pow]; exact haz
    field_simp
    ring
  rw [e1, hrr]; ring

lemma h54e_d2 {p z : ℝ} (hp : 0 < p ∧ p < 1 / 2) (hz : |z| < 1) :
    let a := 1 - 2 * p
    let u := a ^ 2
    let k := 1 - u
    let t := z ^ 2
    let r := Real.sqrt (u + k * t)
    HasDerivAt (h54e_F1 p)
      (-u / (1 - u * t) + k * u * inverseTanh r / r ^ 3 +
        k ^ 2 * t / (r ^ 2 * (1 - r ^ 2))) z := by
  intro a u k t r
  obtain ⟨hu, hk, haz, hr0, hr1⟩ := h54e_dom hp hz
  have hA : HasDerivAt (fun z : ℝ => a * z) a z := by
    simpa using (hasDerivAt_id z).const_mul a
  have h1 := ((h54e_atanh haz).comp z hA).const_mul (-a)
  have hR := h54e_R (z := z) hu hk.le
  have h2 := (h54e_atanh hr1).comp z hR
  have hkz : HasDerivAt (fun z : ℝ => k * z) k z := by
    simpa using (hasDerivAt_id z).const_mul k
  have h3 := ((hkz.mul h2).div hR hr0.ne')
  have := h1.add h3
  have hrr : r ^ 2 = u + k * t := Real.sq_sqrt (by positivity)
  have hr0' : r ≠ 0 := hr0.ne'
  have habs := abs_lt.mp hr1
  have h1r : 1 - r ^ 2 ≠ 0 := by
    have : r < 1 := habs.2
    nlinarith
  have haz' := abs_lt.mp haz
  have h1az : 1 - (a * z) ^ 2 ≠ 0 := by
    have : (a * z) ^ 2 < 1 := by nlinarith
    linarith
  have e := h54e_alg a k z r (inverseTanh r) hr0' h1r h1az hrr
  exact this.congr_deriv e

lemma h54e_ev {p z : ℝ} (hp : 0 < p ∧ p < 1 / 2) (hz : |z| < 1) :
    deriv (diagonalDelta p) =ᶠ[nhds z] h54e_F1 p := by
  have hopen : IsOpen {w : ℝ | |w| < 1} := isOpen_lt continuous_abs continuous_const
  filter_upwards [hopen.mem_nhds hz] with w hw
  exact (h54e_d1 hp hw).deriv

/-- Lemma VIII.2, p.23, Eq.(80): all parameters are constructed from p and z.
The strict domain gives r>0, 1-r^2>0 and 1-u*t>0, including at z=0. -/
theorem solution (p z : ℝ) (hp : 0 < p ∧ p < 1 / 2) (hz : |z| < 1) :
    let a := 1 - 2 * p
    let u := a ^ 2
    let k := 1 - u
    let t := z ^ 2
    let r := Real.sqrt (u + k * t)
    HasDerivAt (deriv (diagonalDelta p))
      (-u / (1 - u * t) + k * u * inverseTanh r / r ^ 3 +
        k ^ 2 * t / (r ^ 2 * (1 - r ^ 2))) z := by
  exact (h54e_d2 hp hz).congr_of_eventuallyEq (h54e_ev hp hz)

end
