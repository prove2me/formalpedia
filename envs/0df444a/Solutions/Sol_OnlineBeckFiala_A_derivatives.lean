-- Prove2me | solution 1 for OnlineBeckFiala.A_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:11:11.74774+00:00
-- url     : https://prove2.me/submissions/b8d5551a-1022-41a1-9341-c911926d00e2

import Mathlib
import Definitions.Def_OnlineBeckFiala_W

section
namespace OnlineBeckFiala

namespace Dev.AD

lemma dpow (p z : ℝ) (hx : 0 < 1 - z ^ 2) :
    HasDerivAt (fun z : ℝ => (1 - z ^ 2) ^ p) (-2 * z * p * (1 - z ^ 2) ^ (p - 1)) z := by
  have h : HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-2 * z) z := by
    simpa using (hasDerivAt_pow 2 z).const_sub 1
  exact h.rpow_const (Or.inl hx.ne')

lemma A_eq (η y : ℝ) (hη : 0 < η) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    A η y ^ (1 + η / 2) = (1 - y ^ 2) ^ (-2 / η - 1) ∧
    A η y ^ (1 + η) = (1 - y ^ 2) ^ (-2 / η - 1 - 1) ∧ 1 ≤ A η y := by
  have hx : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
  refine ⟨?_, ?_, ?_⟩
  · unfold A
    rw [← Real.rpow_mul hx.le]
    congr 1
    field_simp
    ring
  · unfold A
    rw [← Real.rpow_mul hx.le]
    congr 1
    field_simp
    ring
  · unfold A
    apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx (by nlinarith [sq_nonneg y])
    have : 0 < 2 / η := by positivity
    rw [neg_div]; linarith

lemma hasDerivAt_A (η : ℝ) (hη : 0 < η) (y : ℝ) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (A η) (4 * y / η * A η y ^ (1 + η / 2)) y := by
  have hx : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
  have h := dpow (-2 / η) y hx
  rw [(A_eq η y hη hy).1]
  show HasDerivAt (fun z : ℝ => (1 - z ^ 2) ^ (-2 / η)) _ y
  exact h.congr_deriv (by ring)

lemma hasDerivAt_B (η : ℝ) (hη : 0 < η) (y : ℝ) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun z => 4 * z / η * A η z ^ (1 + η / 2))
      (4 / η * A η y ^ (1 + η / 2) + (4 * y / η) ^ 2 * (1 + η / 2) * A η y ^ (1 + η)) y := by
  have hx : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
  have h := ((hasDerivAt_id y).mul (dpow (-2 / η - 1) y hx)).const_mul (4 / η)
  have hev : (fun z => 4 / η * (id z * (1 - z ^ 2) ^ (-2 / η - 1))) =ᶠ[nhds y]
      (fun z => 4 * z / η * A η z ^ (1 + η / 2)) := by
    have : Set.Ioo (-1 : ℝ) 1 ∈ nhds y := Ioo_mem_nhds hy.1 hy.2
    filter_upwards [this] with z hz
    rw [(A_eq η z hη hz).1]
    simp only [id]
    field_simp
  refine (h.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  rw [(A_eq η y hη hy).1, (A_eq η y hη hy).2.1]
  simp only [id]
  field_simp
  ring

lemma iter2 (η : ℝ) (hη : 0 < η) (y : ℝ) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    iteratedDeriv 2 (A η) y =
      4 / η * A η y ^ (1 + η / 2) + (4 * y / η) ^ 2 * (1 + η / 2) * A η y ^ (1 + η) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have : Set.Ioo (-1 : ℝ) 1 ∈ nhds y := Ioo_mem_nhds hy.1 hy.2
  have hev : deriv (A η) =ᶠ[nhds y] (fun z => 4 * z / η * A η z ^ (1 + η / 2)) := by
    filter_upwards [this] with z hz
    exact (hasDerivAt_A η hη z hz).deriv
  rw [hev.deriv_eq]
  exact (hasDerivAt_B η hη y hy).deriv

end Dev.AD

theorem chk_A_derivatives (η : ℝ) (hη : 0 < η) :
    (∀ y ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt (A η) (4 * y / η * A η y ^ (1 + η / 2)) y) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
      0 ≤ iteratedDeriv 2 (A η) y ∧ iteratedDeriv 2 (A η) y ≤ C * A η y ^ (1 + η) := by
  refine ⟨fun y hy => Dev.AD.hasDerivAt_A η hη y hy, ?_⟩
  refine ⟨4 / η + 8 * (2 + η) / η ^ 2, by positivity, fun y hy => ?_⟩
  rw [Dev.AD.iter2 η hη y hy]
  obtain ⟨-, -, h1⟩ := Dev.AD.A_eq η y hη hy
  set a := A η y with ha
  have ha0 : 0 < a := by linarith
  have hp : a ^ (1 + η / 2) ≤ a ^ (1 + η) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  have hp0 : 0 < a ^ (1 + η / 2) := Real.rpow_pos_of_pos ha0 _
  have hq0 : 0 < a ^ (1 + η) := Real.rpow_pos_of_pos ha0 _
  have hy2 : y ^ 2 ≤ 1 := by nlinarith [hy.1, hy.2]
  have e : (4 * y / η) ^ 2 * (1 + η / 2) = 8 * (2 + η) / η ^ 2 * y ^ 2 := by
    field_simp; ring
  rw [show (4 * y / η) ^ 2 * (1 + η / 2) * a ^ (1 + η) = 8 * (2 + η) / η ^ 2 * y ^ 2 * a ^ (1 + η) by rw [e]]
  refine ⟨by positivity, ?_⟩
  have h2 : 8 * (2 + η) / η ^ 2 * y ^ 2 ≤ 8 * (2 + η) / η ^ 2 := by
    have : 0 < 8 * (2 + η) / η ^ 2 := by positivity
    nlinarith
  have hc : 0 < 4 / η := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h2 hq0.le, mul_le_mul_of_nonneg_left hp hc.le]

end OnlineBeckFiala

end

theorem solution : type_of% @OnlineBeckFiala.chk_A_derivatives := @OnlineBeckFiala.chk_A_derivatives
