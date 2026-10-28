-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P40.qubitObjectiveTwo_eq_closedForm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T23:05:46.056814+00:00
-- url     : https://prove2.me/submissions/65173d0d-0419-41a1-abf3-b66215ba1037

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator
open Filter MeasureTheory Asymptotics
open QAlgorithms
open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)
open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
open QAlgorithms.Papers.Independent.Information100.P60 (copies)
open QAlgorithms.Papers.Independent.Information100.P44 (Mat)
namespace QAlgorithms.Papers.Independent.Gap48.P40

namespace CF208

/-- trace-one real symmetric 2x2 matrix with Bloch coordinates (a, b). -/
def Mx (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(((1 + a) / 2 : ℝ) : ℂ), ((b / 2 : ℝ) : ℂ); ((b / 2 : ℝ) : ℂ), (((1 - a) / 2 : ℝ) : ℂ)]

lemma Mx_sa (a b : ℝ) : IsSelfAdjoint (Mx a b) := by
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Mx]

lemma Mx_spec (a b x : ℝ) (hx : x ∈ spectrum ℝ (Mx a b)) :
    x = (1 + Real.sqrt (a ^ 2 + b ^ 2)) / 2 ∨ x = (1 - Real.sqrt (a ^ 2 + b ^ 2)) / 2 := by
  open Polynomial in
  let q : ℝ[X] := X ^ 2 - X + C ((1 - (a ^ 2 + b ^ 2)) / 4)
  have hq : aeval (Mx a b) q = 0 := by
    simp only [q, map_add, map_sub, map_pow, aeval_X, aeval_C]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Mx, sq, Matrix.algebraMap_matrix_apply] <;> ring
  have h := spectrum.subset_polynomial_aeval (Mx a b) q ⟨x, hx, rfl⟩
  rw [hq, spectrum.zero_eq, Set.mem_singleton_iff] at h
  simp only [q, eval_add, eval_sub, eval_pow, eval_X, eval_C] at h
  have hr := Real.sq_sqrt (show 0 ≤ a ^ 2 + b ^ 2 by positivity)
  have : (x - (1 + Real.sqrt (a ^ 2 + b ^ 2)) / 2) * (x - (1 - Real.sqrt (a ^ 2 + b ^ 2)) / 2) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp this with h1 | h1
  · left; linarith
  · right; linarith

lemma Mx_cfc (a b : ℝ) (f : ℝ → ℝ) (p q : ℝ)
    (h1 : f ((1 + Real.sqrt (a ^ 2 + b ^ 2)) / 2) = p * ((1 + Real.sqrt (a ^ 2 + b ^ 2)) / 2) + q)
    (h2 : f ((1 - Real.sqrt (a ^ 2 + b ^ 2)) / 2) = p * ((1 - Real.sqrt (a ^ 2 + b ^ 2)) / 2) + q) :
    cfc f (Mx a b) = !![((p * ((1 + a) / 2) + q : ℝ) : ℂ), ((p * (b / 2) : ℝ) : ℂ);
      ((p * (b / 2) : ℝ) : ℂ), ((p * ((1 - a) / 2) + q : ℝ) : ℂ)] := by
  have hsa := Mx_sa a b
  have hc : cfc f (Mx a b) = cfc (fun x => p * x + q) (Mx a b) := by
    apply cfc_congr
    intro x hx
    rcases Mx_spec a b x hx with rfl | rfl
    · exact h1
    · exact h2
  rw [hc, cfc_add (Mx a b) (fun x => p * x) (fun _ => q), cfc_const_mul p (fun x => x) (Mx a b),
    cfc_id' ℝ (Mx a b), cfc_const q (Mx a b)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mx, Matrix.algebraMap_matrix_apply]

lemma interp (f : ℝ → ℝ) (r : ℝ) : ∃ p q : ℝ, f ((1 + r) / 2) = p * ((1 + r) / 2) + q ∧
    f ((1 - r) / 2) = p * ((1 - r) / 2) + q ∧ (r = 0 → p = 0) := by
  by_cases hr : r = 0
  · subst hr
    exact ⟨0, f (1 / 2), by norm_num, by norm_num, fun _ => rfl⟩
  · refine ⟨(f ((1 + r) / 2) - f ((1 - r) / 2)) / r,
      f ((1 - r) / 2) - (f ((1 + r) / 2) - f ((1 - r) / 2)) / r * ((1 - r) / 2), ?_, ?_,
      fun h => absurd h hr⟩
    · field_simp; ring
    · ring

end CF208

open CF208 in
theorem qubit_cf208 (beta T t : ℝ) (hbeta : 0 < beta ∧ beta ≤ 1 / 2)
    (hT : beta < T ∧ T ≤ 1 - beta) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    qubitObjectiveTwo beta T t =
      (let x := beta - T + (1 - beta - T) * t
       let y2 := (1 - beta - T) ^ 2 * (1 - t ^ 2)
       let rs := Real.sqrt (x ^ 2 + y2)
       let rr := Real.sqrt ((x + 2 * T) ^ 2 + y2)
       let w := ((x + 2 * T) * x + y2) / rs
       (1 + rr) / 2 * Real.log ((1 + rr) / 2) + (1 - rr) / 2 * Real.log ((1 - rr) / 2) -
         ((1 + w) / 2 * Real.log ((1 + rs) / 2) + (1 - w) / 2 * Real.log ((1 - rs) / 2))) := by
  obtain ⟨hb0, hb1⟩ := hbeta
  obtain ⟨hT0, hT1⟩ := hT
  obtain ⟨ht0, ht1⟩ := ht
  set c := 1 - beta - T with hc
  set u := Real.sqrt ((1 + t) / 2) with hu
  set v := Real.sqrt ((1 - t) / 2) with hv
  have hu2 : u * u = (1 + t) / 2 := Real.mul_self_sqrt (by linarith)
  have hv2 : v * v = (1 - t) / 2 := Real.mul_self_sqrt (by linarith)
  have hu2c : (u : ℂ) * u = (1 + (t : ℂ)) / 2 := by
    rw [← Complex.ofReal_mul, hu2]; push_cast; ring
  have hv2c : (v : ℂ) * v = (1 - (t : ℂ)) / 2 := by
    rw [← Complex.ofReal_mul, hv2]; push_cast; ring
  have hcC : (c : ℂ) = 1 - (beta : ℂ) - T := by rw [hc]; push_cast; ring
  have hrho : Matrix.diagonal ![((beta + T : ℝ) : ℂ), 0] +
      ((c : ℝ) : ℂ) • pureDensity (WithLp.toLp 2 ![(u : ℂ), (v : ℂ)] : EuclideanSpace ℂ (Fin 2)) =
      Mx (beta - T + c * t + 2 * T) (2 * c * u * v) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Mx, pureDensity, Complex.conj_ofReal] <;> push_cast
    · rw [hcC]; linear_combination (1 - (beta : ℂ) - T) * hu2c
    · ring
    · ring
    · rw [hcC]; linear_combination (1 - (beta : ℂ) - T) * hv2c
  have hsig : Matrix.diagonal ![(beta : ℂ), (T : ℂ)] +
      ((c : ℝ) : ℂ) • pureDensity (WithLp.toLp 2 ![(u : ℂ), (v : ℂ)] : EuclideanSpace ℂ (Fin 2)) =
      Mx (beta - T + c * t) (2 * c * u * v) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Mx, pureDensity, Complex.conj_ofReal] <;> push_cast
    · rw [hcC]; linear_combination (1 - (beta : ℂ) - T) * hu2c
    · ring
    · ring
    · rw [hcC]; linear_combination (1 - (beta : ℂ) - T) * hv2c
  have hy2 : (2 * c * u * v) ^ 2 = c ^ 2 * (1 - t ^ 2) := by
    have : (2 * c * u * v) ^ 2 = 4 * c ^ 2 * (u * u) * (v * v) := by ring
    rw [this, hu2, hv2]; ring
  unfold qubitObjectiveTwo
  simp only []
  rw [hrho, hsig]
  unfold relativeEntropy
  rw [if_pos]
  swap
  · intro w hw
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw ⊢
    have hdet : (Mx (beta - T + c * t) (2 * c * u * v)).det ≠ 0 := by
      rw [Matrix.det_fin_two]
      simp only [Mx, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
      norm_cast
      have hc0 : 0 ≤ c := by linarith
      have : (1 + (beta - T + c * t)) / 2 * ((1 - (beta - T + c * t)) / 2) -
          2 * c * u * v / 2 * (2 * c * u * v / 2) =
          beta * T + c * (beta * (1 - t) + T * (1 + t)) / 2 := by
        have h4 : 2 * c * u * v / 2 * (2 * c * u * v / 2) = (2 * c * u * v) ^ 2 / 4 := by ring
        rw [h4, hy2, hc]; ring
      rw [this]
      have : 0 ≤ c * (beta * (1 - t) + T * (1 + t)) :=
        mul_nonneg hc0 (by nlinarith)
      nlinarith [mul_pos hb0 (show 0 < T by linarith)]
    rw [Matrix.eq_zero_of_mulVec_eq_zero hdet hw, Matrix.mulVec_zero]
  rw [EReal.toReal_coe]
  set a1 := beta - T + c * t + 2 * T
  set a2 := beta - T + c * t
  set b := 2 * c * u * v
  have hb2 : b ^ 2 = c ^ 2 * (1 - t ^ 2) := hy2
  obtain ⟨p1, q1, e1, e2, -⟩ := interp (fun x : ℝ => x * Real.log x) (Real.sqrt (a1 ^ 2 + b ^ 2))
  obtain ⟨p2, q2, f1, f2, f0⟩ := interp Real.log (Real.sqrt (a2 ^ 2 + b ^ 2))
  rw [Mx_cfc a1 b _ p1 q1 e1 e2, Mx_cfc a2 b _ p2 q2 f1 f2]
  rw [← hb2, e1, e2, f1, f2]
  simp [Mx, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  set rs := Real.sqrt (a2 ^ 2 + b ^ 2)
  by_cases hrs : rs = 0
  · rw [f0 hrs, hrs]; simp; ring
  · field_simp
    ring

end QAlgorithms.Papers.Independent.Gap48.P40

open QAlgorithms.Papers.Independent.Gap48.P40 in
theorem solution (beta T t : ℝ) (hbeta : 0 < beta ∧ beta ≤ 1 / 2)
    (hT : beta < T ∧ T ≤ 1 - beta) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    qubitObjectiveTwo beta T t =
      (let x := beta - T + (1 - beta - T) * t
       let y2 := (1 - beta - T) ^ 2 * (1 - t ^ 2)
       let rs := Real.sqrt (x ^ 2 + y2)
       let rr := Real.sqrt ((x + 2 * T) ^ 2 + y2)
       let w := ((x + 2 * T) * x + y2) / rs
       (1 + rr) / 2 * Real.log ((1 + rr) / 2) + (1 - rr) / 2 * Real.log ((1 - rr) / 2) -
         ((1 + w) / 2 * Real.log ((1 + rs) / 2) + (1 - w) / 2 * Real.log ((1 - rs) / 2))) :=
  QAlgorithms.Papers.Independent.Gap48.P40.qubit_cf208 beta T t hbeta hT ht
