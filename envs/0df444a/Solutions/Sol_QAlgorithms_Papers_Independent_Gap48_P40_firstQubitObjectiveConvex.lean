-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P40.firstQubitObjectiveConvex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T00:51:46.604335+00:00
-- url     : https://prove2.me/submissions/1d49a0b1-43f5-4d5f-85d1-691d0916a825

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

open Real Set


theorem p40_int_inv (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∫ s in (0:ℝ)..1, 1/(1 - r^2*s^2) = (log (1+r) - log (1-r))/(2*r) := by
  have hpos : ∀ s ∈ uIcc (0:ℝ) 1, 0 < 1 - r*s ∧ 0 < 1 + r*s ∧ 0 < 1 - r^2*s^2 := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    obtain ⟨h0, h1⟩ := hs
    have : r*s < 1 := by nlinarith
    have : 0 ≤ r*s := by positivity
    refine ⟨by linarith, by linarith, by nlinarith⟩
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => (log (1+r*s) - log (1-r*s))/(2*r))
    (f' := fun s => 1/(1 - r^2*s^2)) (a := 0) (b := 1) ?_ ?_
  · rw [this]; simp
  · intro s hs
    obtain ⟨h1, h2, h3⟩ := hpos s hs
    have d2 : HasDerivAt (fun s => 1 + r*s) r s := by
      simpa using ((hasDerivAt_id s).const_mul r).const_add 1
    have d3 : HasDerivAt (fun s => 1 - r*s) (-r) s := by
      simpa using ((hasDerivAt_id s).const_mul r).const_sub 1
    have := ((d2.log h2.ne').sub (d3.log h1.ne')).div_const (2*r)
    refine this.congr_deriv ?_
    have e : 1 - r^2*s^2 = (1+r*s)*(1-r*s) := by ring
    rw [e]; field_simp; ring
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro s hs; exact (hpos s hs).2.2.ne'

theorem p40_h_deriv (r : ℝ) (hr0 : -1 < r) (hr1 : r < 1) :
    HasDerivAt (fun r : ℝ => (1+r)/2 * log ((1+r)/2) + (1-r)/2 * log ((1-r)/2))
      ((log (1+r) - log (1-r))/2) r := by
  have p1 : 0 < (1+r)/2 := by linarith
  have p2 : 0 < (1-r)/2 := by linarith
  have d1 : HasDerivAt (fun r : ℝ => (1+r)/2) (1/2) r := by
    simpa using ((hasDerivAt_id r).const_add 1).div_const 2
  have d2 : HasDerivAt (fun r : ℝ => (1-r)/2) (-(1/2)) r := by
    simpa [neg_div] using ((hasDerivAt_id r).const_sub 1).div_const 2
  have := (d1.mul (d1.log p1.ne')).add (d2.mul (d2.log p2.ne'))
  refine this.congr_deriv ?_
  rw [log_div (by linarith) (by norm_num), log_div (by linarith) (by norm_num)]
  have : 1 + r ≠ 0 := by linarith
  have : 1 - r ≠ 0 := by linarith
  field_simp
  ring

theorem p40_F_convex0 :
    ConvexOn ℝ (Icc (0:ℝ) 1) (fun a : ℝ => (1+√a)/2 * log ((1+√a)/2) + (1-√a)/2 * log ((1-√a)/2)) := by
  have hd : ∀ a ∈ Ioo (0:ℝ) 1, HasDerivAt
      (fun a : ℝ => (1+√a)/2 * log ((1+√a)/2) + (1-√a)/2 * log ((1-√a)/2))
      (∫ s in (0:ℝ)..1, 1/(1 - a*s^2) / 2) a := by
    intro a ha
    have hs0 : 0 < √a := Real.sqrt_pos.2 ha.1
    have hs1 : √a < 1 := by
      rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt ha.1.le ha.2
    have := (p40_h_deriv (√a) (by linarith) hs1).comp a (Real.hasDerivAt_sqrt ha.1.ne')
    refine this.congr_deriv ?_
    rw [intervalIntegral.integral_div]
    have := p40_int_inv (√a) hs0 hs1
    rw [Real.sq_sqrt ha.1.le] at this
    rw [this]
    field_simp
  refine MonotoneOn.convexOn_of_deriv (convex_Icc _ _) ?_ ?_ ?_
  · apply Continuous.continuousOn
    exact (Real.continuous_mul_log.comp (by fun_prop : Continuous fun a : ℝ => (1+√a)/2)).add
      (Real.continuous_mul_log.comp (by fun_prop : Continuous fun a : ℝ => (1-√a)/2))
  · rw [interior_Icc]; intro a ha; exact (hd a ha).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro a ha b hb hab
    rw [(hd a ha).deriv, (hd b hb).deriv]
    have pos : ∀ c ∈ Ioo (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1, 0 < 1 - c*s^2 := by
      intro c hc s hs
      have : s^2 ≤ 1 := by nlinarith [hs.1, hs.2]
      nlinarith [hc.1, hc.2]
    have ii : ∀ c ∈ Ioo (0:ℝ) 1, IntervalIntegrable (fun s : ℝ => 1/(1 - c*s^2) / 2)
        MeasureTheory.volume 0 1 := by
      intro c hc
      apply ContinuousOn.intervalIntegrable
      refine (ContinuousOn.div continuousOn_const (by fun_prop) ?_).div_const _
      intro s hs; rw [uIcc_of_le zero_le_one] at hs; exact (pos c hc s hs).ne'
    apply intervalIntegral.integral_mono_on zero_le_one (ii a ha) (ii b hb)
    intro s hs
    have h1 := pos a ha s hs
    have h2 := pos b hb s hs
    have : 1/(1 - a*s^2) ≤ 1/(1 - b*s^2) := by
      apply one_div_le_one_div_of_le h2
      nlinarith [sq_nonneg s]
    linarith

noncomputable def p40F (a : ℝ) : ℝ := (1+√a)/2 * log ((1+√a)/2) + (1-√a)/2 * log ((1-√a)/2)

theorem p40_F_convex : ConvexOn ℝ (Icc (0:ℝ) 1) p40F := p40_F_convex0

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

namespace QAlgorithms.Papers.Independent.Gap48.P40

open CF208 in
theorem qubit_one_cf (beta T t : ℝ) (hbeta : 0 < beta ∧ beta ≤ 1 / 2)
    (hT : 0 ≤ T ∧ T ≤ beta) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    qubitObjectiveOne beta T t =
      (let x := (1 - 2 * beta) * t
       let y2 := (1 - 2 * beta) ^ 2 * (1 - t ^ 2)
       let rs := Real.sqrt (x ^ 2 + y2)
       let rr := Real.sqrt ((x + 2 * T) ^ 2 + y2)
       let w := ((x + 2 * T) * x + y2) / rs
       (1 + rr) / 2 * Real.log ((1 + rr) / 2) + (1 - rr) / 2 * Real.log ((1 - rr) / 2) -
         ((1 + w) / 2 * Real.log ((1 + rs) / 2) + (1 - w) / 2 * Real.log ((1 - rs) / 2))) := by
  obtain ⟨hb0, hb1⟩ := hbeta
  obtain ⟨hT0, hT1⟩ := hT
  obtain ⟨ht0, ht1⟩ := ht
  set c := 1 - 2 * beta with hc
  set u := Real.sqrt ((1 + t) / 2) with hu
  set v := Real.sqrt ((1 - t) / 2) with hv
  have hu2 : u * u = (1 + t) / 2 := Real.mul_self_sqrt (by linarith)
  have hv2 : v * v = (1 - t) / 2 := Real.mul_self_sqrt (by linarith)
  have hu2c : (u : ℂ) * u = (1 + (t : ℂ)) / 2 := by
    rw [← Complex.ofReal_mul, hu2]; push_cast; ring
  have hv2c : (v : ℂ) * v = (1 - (t : ℂ)) / 2 := by
    rw [← Complex.ofReal_mul, hv2]; push_cast; ring
  have hcC : (c : ℂ) = 1 - 2 * (beta : ℂ) := by rw [hc]; push_cast; ring
  have hrho : Matrix.diagonal ![((beta + T : ℝ) : ℂ), ((beta - T : ℝ) : ℂ)] +
      ((c : ℝ) : ℂ) • pureDensity (WithLp.toLp 2 ![(u : ℂ), (v : ℂ)] : EuclideanSpace ℂ (Fin 2)) =
      Mx (c * t + 2 * T) (2 * c * u * v) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Mx, pureDensity, Complex.conj_ofReal] <;> push_cast
    · rw [hcC]; linear_combination (1 - 2 * (beta : ℂ)) * hu2c
    · ring
    · ring
    · rw [hcC]; linear_combination (1 - 2 * (beta : ℂ)) * hv2c
  have hsig : Matrix.diagonal ![(beta : ℂ), (beta : ℂ)] +
      ((c : ℝ) : ℂ) • pureDensity (WithLp.toLp 2 ![(u : ℂ), (v : ℂ)] : EuclideanSpace ℂ (Fin 2)) =
      Mx (c * t) (2 * c * u * v) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Mx, pureDensity, Complex.conj_ofReal] <;> push_cast
    · rw [hcC]; linear_combination (1 - 2 * (beta : ℂ)) * hu2c
    · ring
    · ring
    · rw [hcC]; linear_combination (1 - 2 * (beta : ℂ)) * hv2c
  have hy2 : (2 * c * u * v) ^ 2 = c ^ 2 * (1 - t ^ 2) := by
    have : (2 * c * u * v) ^ 2 = 4 * c ^ 2 * (u * u) * (v * v) := by ring
    rw [this, hu2, hv2]; ring
  unfold qubitObjectiveOne
  simp only []
  rw [hrho, hsig]
  unfold relativeEntropy
  rw [if_pos]
  swap
  · intro w hw
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw ⊢
    have hdet : (Mx (c * t) (2 * c * u * v)).det ≠ 0 := by
      rw [Matrix.det_fin_two]
      simp only [Mx, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
      norm_cast
      have : (1 + c * t) / 2 * ((1 - c * t) / 2) -
          2 * c * u * v / 2 * (2 * c * u * v / 2) = beta * (1 - beta) := by
        have h4 : 2 * c * u * v / 2 * (2 * c * u * v / 2) = (2 * c * u * v) ^ 2 / 4 := by ring
        rw [h4, hy2, hc]; ring
      rw [this]
      have : 0 < 1 - beta := by linarith
      positivity
    rw [Matrix.eq_zero_of_mulVec_eq_zero hdet hw, Matrix.mulVec_zero]
  rw [EReal.toReal_coe]
  set a1 := c * t + 2 * T
  set a2 := c * t
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

theorem p40_comp_affine (A0 A1 m k : ℝ) (hA : ∀ t ∈ Icc (-1:ℝ) 1, A0 + A1 * t ∈ Icc (0:ℝ) 1) :
    ConvexOn ℝ (Icc (-1:ℝ) 1) (fun t => p40F (A0 + A1 * t) + (m * t + k)) := by
  refine ⟨convex_Icc _ _, fun x hx y hy θ1 θ2 h1 h2 hs => ?_⟩
  have := p40_F_convex.2 (hA x hx) (hA y hy) h1 h2 hs
  simp only [smul_eq_mul] at this ⊢
  have e : θ1 * (A0 + A1 * x) + θ2 * (A0 + A1 * y) = A0 + A1 * (θ1 * x + θ2 * y) := by
    have : θ2 = 1 - θ1 := by linarith
    subst this; ring
  rw [e] at this
  have : θ2 = 1 - θ1 := by linarith
  subst this
  nlinarith

open QAlgorithms.Papers.Independent.Gap48.P40 in
theorem solution (beta T : ℝ) (hbeta : 0 < beta ∧ beta ≤ 1 / 2)
    (hT : 0 ≤ T ∧ T ≤ beta) :
    ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (qubitObjectiveOne beta T) := by
  obtain ⟨hb0, hb1⟩ := hbeta
  obtain ⟨hT0, hT1⟩ := hT
  set c := 1 - 2 * beta with hc
  have hc0 : 0 ≤ c := by linarith
  -- w is affine in t
  obtain ⟨α, γ, hw⟩ : ∃ α γ : ℝ, ∀ t : ℝ,
      ((c * t + 2 * T) * (c * t) + c ^ 2 * (1 - t ^ 2)) / Real.sqrt ((c * t) ^ 2 + c ^ 2 * (1 - t ^ 2))
        = α * t + γ := by
    have hs : ∀ t : ℝ, Real.sqrt ((c * t) ^ 2 + c ^ 2 * (1 - t ^ 2)) = c := by
      intro t
      rw [show (c * t) ^ 2 + c ^ 2 * (1 - t ^ 2) = c ^ 2 by ring, Real.sqrt_sq hc0]
    rcases hc0.eq_or_lt with h | h
    · refine ⟨0, 0, fun t => ?_⟩
      rw [hs, ← h]; simp
    · refine ⟨2 * T, c, fun t => ?_⟩
      rw [hs]; field_simp; ring
  have hrs : Real.sqrt ((c * 1) ^ 2 + c ^ 2 * (1 - 1 ^ 2)) = c := by
    rw [show (c * 1) ^ 2 + c ^ 2 * (1 - 1 ^ 2) = c ^ 2 by ring, Real.sqrt_sq hc0]
  set L1 := Real.log ((1 + c) / 2)
  set L2 := Real.log ((1 - c) / 2)
  have hconv := p40_comp_affine (4 * T ^ 2 + c ^ 2) (4 * T * c)
    (-(α / 2 * L1 - α / 2 * L2)) (-((1 + γ) / 2 * L1 + (1 - γ) / 2 * L2)) ?_
  · refine hconv.congr ?_
    intro t ht
    rw [qubit_one_cf beta T t ⟨hb0, hb1⟩ ⟨hT0, hT1⟩ ht]
    simp only []
    rw [hw t]
    have hs : Real.sqrt ((c * t) ^ 2 + c ^ 2 * (1 - t ^ 2)) = c := by
      rw [show (c * t) ^ 2 + c ^ 2 * (1 - t ^ 2) = c ^ 2 by ring, Real.sqrt_sq hc0]
    rw [hs, p40F, show 4 * T ^ 2 + c ^ 2 + 4 * T * c * t = (c * t + 2 * T) ^ 2 + c ^ 2 * (1 - t ^ 2) by ring]
    ring
  · intro t ht
    obtain ⟨h1, h2⟩ := ht
    constructor
    · nlinarith [sq_nonneg (c * t + 2 * T), mul_nonneg (sq_nonneg c) (show 0 ≤ (1 - t) * (1 + t) by nlinarith)]
    · nlinarith [mul_nonneg (mul_nonneg hT0 hc0) (show 0 ≤ 1 - t by linarith)]
