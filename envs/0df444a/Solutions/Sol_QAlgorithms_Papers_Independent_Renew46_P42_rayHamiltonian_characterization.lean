-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P42.rayHamiltonian_characterization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T12:28:24.910994+00:00
-- url     : https://prove2.me/submissions/dffd3320-6898-45c3-82a5-4f0b4f69804e

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42
open QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)
theorem x6r_cp {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (i : Fin d)
    (hf : DifferentiableAt ℝ f x) :
    cartesianPartial f x i = deriv (fun t : ℝ => f (x + t • Pi.single i 1)) 0 := by
  have hL : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) => WithLp.ofLp y)
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ) : EuclideanSpace ℝ (Fin d) →L[ℝ] (Fin d → ℝ))
      (WithLp.toLp 2 x) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap.hasFDerivAt
  have hf' : HasFDerivAt f (fderiv ℝ f x) (WithLp.ofLp (WithLp.toLp 2 x)) := hf.hasFDerivAt
  have hc := hf'.comp (WithLp.toLp 2 x) hL
  have hline : HasDerivAt (fun t : ℝ => x + t • Pi.single i (1:ℝ)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (Pi.single i (1:ℝ))).const_add x
  have h2 := (by simpa using hf.hasFDerivAt : HasFDerivAt f (fderiv ℝ f x) (x + (0:ℝ) • Pi.single i 1)).comp_hasDerivAt (0:ℝ) hline
  rw [show (fun t : ℝ => f (x + t • Pi.single i 1)) = (f ∘ fun t => x + t • Pi.single i 1) from rfl,
    h2.deriv, cartesianPartial, QAlgorithms.Papers.Independent.Dependency50.P20.coordinatePartial]
  simp only
  rw [show (fun y : EuclideanSpace ℝ (Fin d) => f (WithLp.ofLp y)) = f ∘ WithLp.ofLp from rfl, hc.fderiv]
  simp [EuclideanSpace.single]
  congr 1

theorem x6r_dot_line (v k : V3) (j : Fin 3) (t : ℝ) :
    dot3 v (k + t • Pi.single j 1) = dot3 v k + t * v j := by
  fin_cases j <;> simp [dot3, Fin.sum_univ_three] <;> ring

theorem x6r_dot_line2 (k : V3) (j : Fin 3) (t : ℝ) :
    dot3 (k + t • Pi.single j 1) (k + t • Pi.single j 1) = dot3 k k + 2 * t * k j + t ^ 2 := by
  fin_cases j <;> simp [dot3, Fin.sum_univ_three] <;> ring

theorem x6r_grad (c n : ℝ) (u k : V3) (j : Fin 3)
    (hA : 0 < c ^ 2 * dot3 k k -
      ((n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u)) * (dot3 u k) ^ 2) :
    rayVelocity c n u k j =
      Real.sqrt ((c ^ 2 - dot3 u u) / (n ^ 2 * c ^ 2 - dot3 u u)) *
        ((c ^ 2 * k j - ((n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u)) * dot3 u k * u j) /
          Real.sqrt (c ^ 2 * dot3 k k -
            ((n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u)) * (dot3 u k) ^ 2)) +
      ((n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u)) * u j := by
  set α := (n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u) with hα
  set s := Real.sqrt ((c ^ 2 - dot3 u u) / (n ^ 2 * c ^ 2 - dot3 u u)) with hs
  have hdiff : DifferentiableAt ℝ (rayHamiltonian c n u) k := by
    have hd : DifferentiableAt ℝ (fun k' : V3 => c ^ 2 * dot3 k' k' - α * dot3 u k' ^ 2) k := by
      unfold dot3; fun_prop
    have hd2 : DifferentiableAt ℝ (fun k' : V3 => dot3 u k') k := by
      unfold dot3; fun_prop
    have := ((hd.sqrt hA.ne').const_mul s).add (hd2.const_mul α)
    exact this
  rw [rayVelocity]
  unfold QAlgorithms.Papers.Independent.Renew46.P42.gradient
  rw [x6r_cp _ _ _ hdiff]
  have hfun : (fun t : ℝ => rayHamiltonian c n u (k + t • Pi.single j 1)) =
      fun t => s * Real.sqrt (c ^ 2 * (dot3 k k + (2 * k j * t + t ^ 2)) - α * (dot3 u k + u j * t) ^ 2) +
        α * (dot3 u k + u j * t) := by
    funext t
    rw [rayHamiltonian, x6r_dot_line2, x6r_dot_line]
    have e1 : dot3 k k + 2 * t * k j + t ^ 2 = dot3 k k + (2 * k j * t + t ^ 2) := by ring
    have e2 : dot3 u k + t * u j = dot3 u k + u j * t := by ring
    rw [e1, e2]
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => dot3 k k + (2 * k j * t + t ^ 2)) (2 * k j * 1 + ((2:ℕ):ℝ) * 0 ^ (2 - 1) * 1) 0 :=
    (((hasDerivAt_id' (0:ℝ)).const_mul (2 * k j)).add ((hasDerivAt_id' (0:ℝ)).pow 2)).const_add _
  have h2 : HasDerivAt (fun t : ℝ => dot3 u k + u j * t) (u j * 1) 0 :=
    ((hasDerivAt_id' (0:ℝ)).const_mul (u j)).const_add _
  have hg := (h1.const_mul (c ^ 2)).sub ((h2.pow 2).const_mul α)
  have hg0 : c ^ 2 * (dot3 k k + (2 * k j * 0 + 0 ^ 2)) - α * (dot3 u k + u j * 0) ^ 2 ≠ 0 := by
    simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact hA.ne'
  have hh := ((hg.sqrt hg0).const_mul s).add (h2.const_mul α)
  refine hh.deriv.trans ?_
  have hr : Real.sqrt (c ^ 2 * dot3 k k - α * dot3 u k ^ 2) ≠ 0 := (Real.sqrt_pos.2 hA).ne'
  simp only [Pi.sub_apply, Pi.pow_apply, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_one]
  field_simp
  ring

theorem x6r_K (c n ω : ℝ) (u k : V3) :
    let K := apply4 (gUp c n u) (waveCovector c ω k)
    K 0 = ω / c + (n ^ 2 - 1) * lorentzFactor c u ^ 2 * (ω - dot3 u k) / c ∧
    (∀ j : Fin 3, spatial K j = k j + (n ^ 2 - 1) * lorentzFactor c u ^ 2 * (ω - dot3 u k) * u j / c ^ 2) := by
  intro K
  refine ⟨?_, ?_⟩
  · simp only [K, apply4, gUp, minkowskiMetric, fourFlow, waveCovector, Fin.sum_univ_four, dot3,
      Fin.sum_univ_three]
    simp
    ring
  · intro j
    fin_cases j <;>
    · simp only [K, spatial, apply4, gUp, minkowskiMetric, fourFlow, waveCovector, Fin.sum_univ_four, dot3,
        Fin.sum_univ_three]
      simp
      ring

theorem x6r_cauchy (u k : V3) : dot3 u k ^ 2 ≤ dot3 u u * dot3 k k := by
  simp only [dot3, Fin.sum_univ_three]
  nlinarith [sq_nonneg (u 0 * k 1 - u 1 * k 0), sq_nonneg (u 0 * k 2 - u 2 * k 0),
    sq_nonneg (u 1 * k 2 - u 2 * k 1)]

theorem x6r_dot_pos (k : V3) (hk : k ≠ 0) : 0 < dot3 k k := by
  have : ∃ i, k i ≠ 0 := by
    by_contra h; push Not at h; exact hk (funext h)
  obtain ⟨i, hi⟩ := this
  have hsq : ∀ i, 0 ≤ k i * k i := fun i => mul_self_nonneg _
  simp only [dot3, Fin.sum_univ_three]
  fin_cases i <;> simp at hi <;> nlinarith [hsq 0, hsq 1, hsq 2, mul_self_pos.2 hi]

theorem x6r_dot_nonneg (u : V3) : 0 ≤ dot3 u u := by
  simp only [dot3, Fin.sum_univ_three]
  nlinarith [mul_self_nonneg (u 0), mul_self_nonneg (u 1), mul_self_nonneg (u 2)]

theorem x6r_dot_smul_right (u k : V3) (a : ℝ) : dot3 u (a • k) = a * dot3 u k := by
  simp only [dot3, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]; ring

theorem x6r_dot_smul_left (u k : V3) (a : ℝ) : dot3 (a • k) u = a * dot3 k u := by
  simp only [dot3, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]; ring

theorem x6r_dot_comm (u k : V3) : dot3 u k = dot3 k u := by
  simp only [dot3, Fin.sum_univ_three]; ring

theorem x6r_dot_add_right (u v w : V3) : dot3 u (v + w) = dot3 u v + dot3 u w := by
  simp only [dot3, Fin.sum_univ_three, Pi.add_apply]; ring

theorem x6r_dot_add_left (u v w : V3) : dot3 (v + w) u = dot3 v u + dot3 w u := by
  simp only [dot3, Fin.sum_univ_three, Pi.add_apply]; ring

theorem x6r_cross (a u : V3) :
    cross3 a (cross3 u a) = dot3 a a • u - dot3 a u • a := by
  funext i
  fin_cases i <;> simp [cross3, dot3, Fin.sum_univ_three] <;> ring

theorem x6r_part3 (c n : ℝ) (k : V3) (hc : 0 < c) (hn : 1 ≤ n) :
    rayHamiltonian c n 0 k = c * length3 k / n := by
  have hd0 : dot3 0 0 = 0 := by simp [dot3]
  have hd1 : dot3 0 k = 0 := by simp [dot3]
  have hn0 : 0 < n := by linarith
  rw [rayHamiltonian, hd0, hd1, length3,
    show (c ^ 2 - 0) / (n ^ 2 * c ^ 2 - 0) = (1 / n) ^ 2 by field_simp; ring,
    Real.sqrt_sq (by positivity),
    show c ^ 2 * dot3 k k - (n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - 0) * 0 ^ 2
      = c ^ 2 * dot3 k k by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hc.le]
  ring

theorem x6r_hw (v u : V3) (a : ℝ) : v - u + a • u = v + (a - 1) • u := by
  funext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem x6r_final (c n γ e s V W : ℝ) (hc2 : 0 < c ^ 2) (hγ0 : 0 < γ) (hce : 0 < c ^ 2 - e)
    (hn0 : n ≠ 0)
    (hcW' : c ^ 2 * W = γ ^ 2 * (V * (c ^ 2 - s) + c ^ 2 * s + e ^ 2 - 2 * c ^ 2 * e))
    (hZ' : (n ^ 2 - 1) * (c ^ 2 - e) ^ 2 - n ^ 2 * (c ^ 2 - s) * (c ^ 2 - V) = 0) :
    1 / (γ * (1 - e / c ^ 2)) * (1 / (γ * (1 - e / c ^ 2)) * W) = c ^ 2 / n ^ 2 := by
  have hγn : γ ≠ 0 := hγ0.ne'
  have hce' : c ^ 2 - e ≠ 0 := hce.ne'
  have hc0 : c ^ 2 ≠ 0 := hc2.ne'
  have h1 : 1 - e / c ^ 2 = (c ^ 2 - e) / c ^ 2 := by rw [sub_div, div_self hc0]
  rw [h1]
  field_simp
  linear_combination c ^ 2 * n ^ 2 * hcW' + c ^ 2 * γ ^ 2 * hZ'

set_option maxHeartbeats 2000000 in
theorem solution (c n : ℝ) (u k : V3)
    (hc : 0 < c) (hn : 1 ≤ n) (hu : dot3 u u < c ^ 2) (hk : k ≠ 0) :
    rayDispersion c n u k (rayHamiltonian c n u k) = 0 ∧
    (∀ omega : ℝ, (rayDispersion c n u k omega = 0 ∧ 0 < omega - dot3 u k) ↔
      omega = rayHamiltonian c n u k) ∧
    rayHamiltonian c n 0 k = c * length3 k / n ∧
    dot3 (comovingVelocity c u (rayVelocity c n u k))
      (comovingVelocity c u (rayVelocity c n u k)) = c ^ 2 / n ^ 2 ∧
    rayHamiltonian c n u k = length3 k *
      directionalH c n u (dot3 u ((1 / length3 k) • k)) ∧
    rayVelocity c n u k =
      directionalH c n u (dot3 u ((1 / length3 k) • k)) • ((1 / length3 k) • k) +
      deriv (directionalH c n u) (dot3 u ((1 / length3 k) • k)) •
        cross3 ((1 / length3 k) • k) (cross3 u ((1 / length3 k) • k)) ∧
    (∀ a : ℝ, 0 < a →
      rayHamiltonian c n u (a • k) = a * rayHamiltonian c n u k ∧
      rayVelocity c n u (a • k) = rayVelocity c n u k) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hn2 : 1 ≤ n ^ 2 := by nlinarith
  have hs0 := x6r_dot_nonneg u
  have hq := x6r_dot_pos k hk
  have hCS := x6r_cauchy u k
  have hN : 0 < n ^ 2 * c ^ 2 - dot3 u u := by nlinarith
  have hcs : 0 < c ^ 2 - dot3 u u := by linarith
  have hpos : 0 < 1 - dot3 u u / c ^ 2 := by rw [sub_pos, div_lt_one hc2]; exact hu
  have hγ2 : lorentzFactor c u ^ 2 = c ^ 2 / (c ^ 2 - dot3 u u) := by
    rw [lorentzFactor, div_pow, Real.sq_sqrt hpos.le]; field_simp
  have hγ0 : 0 < lorentzFactor c u := by
    rw [lorentzFactor]; exact div_pos one_pos (Real.sqrt_pos.2 hpos)
  have hlen : length3 k ^ 2 = dot3 k k := Real.sq_sqrt (x6r_dot_nonneg k)
  have hL0 : 0 < length3 k := Real.sqrt_pos.2 hq
  set s := dot3 u u with hs
  set p := dot3 u k with hp
  set q := dot3 k k with hqd
  set L := length3 k with hL
  set B := (n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - s) with hB
  set A := Real.sqrt ((c ^ 2 - s) / (n ^ 2 * c ^ 2 - s)) with hA
  have hBD : B * (n ^ 2 * c ^ 2 - s) = n ^ 2 * c ^ 2 - c ^ 2 := by rw [hB]; field_simp
  have hB0 : 0 ≤ B := div_nonneg (by nlinarith) hN.le
  have hB1 : B < 1 := by rw [hB, div_lt_one hN]; linarith
  have hApos : 0 < A := Real.sqrt_pos.2 (div_pos hcs hN)
  have hA2 : A ^ 2 = 1 - B := by
    rw [hA, Real.sq_sqrt (div_pos hcs hN).le, hB, eq_sub_iff_add_eq, ← add_div,
      div_eq_one_iff_eq hN.ne']
    ring
  have hnA : n ^ 2 * c ^ 2 * A ^ 2 = c ^ 2 - B * s := by
    rw [hA2]; linear_combination (-1 : ℝ) * hBD
  have hcBs : 0 < c ^ 2 - B * s := by nlinarith
  set Q := c ^ 2 * q - B * p ^ 2 with hQ
  have hQ0 : 0 < Q := by nlinarith
  set R := Real.sqrt Q with hR
  have hR0 : 0 < R := Real.sqrt_pos.2 hQ0
  have hR2 : R ^ 2 = Q := Real.sq_sqrt hQ0.le
  have hRAp : R ^ 2 - (A * p) ^ 2 = c ^ 2 * q - p ^ 2 := by rw [hR2, mul_pow, hA2]; ring
  have hcq : 0 < c ^ 2 * q - p ^ 2 := by nlinarith
  have hAp1 : A * p < R := by nlinarith
  have hAp2 : -R < A * p := by nlinarith
  have hH : rayHamiltonian c n u k = A * R + B * p := rfl
  have hvel : ∀ k' : V3, 0 < c ^ 2 * dot3 k' k' - B * dot3 u k' ^ 2 →
      rayVelocity c n u k' = (A * c ^ 2 / Real.sqrt (c ^ 2 * dot3 k' k' - B * dot3 u k' ^ 2)) • k' +
        (B - A * B * dot3 u k' / Real.sqrt (c ^ 2 * dot3 k' k' - B * dot3 u k' ^ 2)) • u := by
    intro k' hk'
    have hr : Real.sqrt (c ^ 2 * dot3 k' k' - B * dot3 u k' ^ 2) ≠ 0 := (Real.sqrt_pos.2 hk').ne'
    funext j
    rw [x6r_grad c n u k' j hk', ← hs, ← hB, ← hA]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hdir : ∀ z, directionalH c n u z = A * Real.sqrt (c ^ 2 - B * z ^ 2) + B * z := fun z => rfl
  have hHk : ∀ k' : V3, rayHamiltonian c n u k' =
      A * Real.sqrt (c ^ 2 * dot3 k' k' - B * dot3 u k' ^ 2) + B * dot3 u k' := fun k' => rfl
  clear_value s p q L B A Q R
  -- dispersion factorisation
  have hK : (n ^ 2 - 1) * lorentzFactor c u ^ 2 * A ^ 2 = B := by
    rw [hγ2, hA, Real.sq_sqrt (div_pos hcs hN).le, hB]; field_simp
  have hfac : ∀ ω, A ^ 2 * rayDispersion c n u k ω = (ω - (A * R + B * p)) * (ω - (B * p - A * R)) := by
    intro ω
    simp only [rayDispersion]
    rw [← hp, ← hqd]
    linear_combination (ω - p) ^ 2 * hK + (ω ^ 2 - B * p ^ 2) * hA2 + A ^ 2 * hR2 + A ^ 2 * hQ
  have hA2pos : 0 < A ^ 2 := by positivity
  have hdisp : rayDispersion c n u k (A * R + B * p) = 0 := by
    have := hfac (A * R + B * p)
    rw [sub_self, zero_mul] at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hA2pos.ne'
    · exact h
  have hpos : 0 < c ^ 2 * dot3 k k - B * dot3 u k ^ 2 := by rw [← hqd, ← hp, ← hQ]; exact hQ0
  have hζ : dot3 u ((1 / L) • k) = p / L := by rw [x6r_dot_smul_right, ← hp]; ring
  have hr : Real.sqrt (c ^ 2 - B * (p / L) ^ 2) = R / L := by
    rw [show c ^ 2 - B * (p / L) ^ 2 = (R / L) ^ 2 by simp only [div_pow]; rw [hR2, hlen, hQ]; field_simp]
    exact Real.sqrt_sq (by positivity)
  have hderiv : deriv (directionalH c n u) (p / L) =
      A * (-(B * (2 * (p / L))) / (2 * Real.sqrt (c ^ 2 - B * (p / L) ^ 2))) + B := by
    have h1 : HasDerivAt (fun z : ℝ => c ^ 2 - B * z ^ 2) (-(B * (2 * (p / L)))) (p / L) := by
      have := ((hasDerivAt_pow 2 (p / L)).const_mul B).const_sub (c ^ 2)
      exact this.congr_deriv (by norm_num)
    have h2 : c ^ 2 - B * (p / L) ^ 2 ≠ 0 := by
      rw [show c ^ 2 - B * (p / L) ^ 2 = (R / L) ^ 2 by simp only [div_pow]; rw [hR2, hlen, hQ]; field_simp]
      positivity
    have h3 := ((h1.sqrt h2).const_mul A).add ((hasDerivAt_id (p / L)).const_mul B)
    have h4 : HasDerivAt (fun z => A * Real.sqrt (c ^ 2 - B * z ^ 2) + B * z)
      (A * (-(B * (2 * (p / L))) / (2 * Real.sqrt (c ^ 2 - B * (p / L) ^ 2))) + B * 1) (p / L) := h3
    rw [show directionalH c n u = fun z => A * Real.sqrt (c ^ 2 - B * z ^ 2) + B * z from
      funext fun z => hdir z, h4.deriv, mul_one]
  refine ⟨by rw [hH]; exact hdisp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω
    rw [hH]
    constructor
    · rintro ⟨h0, h1⟩
      have := hfac ω
      rw [h0, mul_zero] at this
      rcases mul_eq_zero.1 this.symm with h | h
      · linarith
      · exfalso
        have h2 : ω = B * p - A * R := by linarith
        rw [h2] at h1
        have h3 : B * p - A * R - p = -(A * (R + A * p)) := by linear_combination p * hA2
        have h4 : 0 < A * (R + A * p) := mul_pos hApos (by linarith)
        linarith
    · rintro rfl
      refine ⟨hdisp, ?_⟩
      have h3 : A * R + B * p - p = A * (R - A * p) := by linear_combination p * hA2
      have h4 : 0 < A * (R - A * p) := mul_pos hApos (by linarith)
      linarith
  · rw [hL]; exact x6r_part3 c n k hc hn
  · rw [hvel k hpos, ← hqd, ← hp, ← hQ, ← hR]
    generalize hα : A * c ^ 2 / R = α
    generalize hβ : B - A * B * p / R = β
    have hα' : α * R = A * c ^ 2 := by rw [← hα]; field_simp
    have hβ' : β * R = B * (R - A * p) := by rw [← hβ]; field_simp
    have he : dot3 u (α • k + β • u) = α * p + β * s := by
      rw [x6r_dot_add_right, x6r_dot_smul_right, x6r_dot_smul_right, ← hp, ← hs]
    have hV : dot3 (α • k + β • u) (α • k + β • u) = α ^ 2 * q + 2 * α * β * p + β ^ 2 * s := by
      simp only [x6r_dot_add_left, x6r_dot_add_right, x6r_dot_smul_left, x6r_dot_smul_right]
      rw [x6r_dot_comm k u, ← hp, ← hqd, ← hs]; ring
    generalize hvd : α • k + β • u = v at he hV
    generalize hed : dot3 u v = e at he
    generalize hVd : dot3 v v = V at hV
    have key1 : R * (c ^ 2 - e) = (c ^ 2 - B * s) * (R - A * p) := by
      rw [he]; linear_combination (-p) * hα' + (-s) * hβ'
    have hRV : R ^ 2 * V = (A * c ^ 2) ^ 2 * q + 2 * (A * c ^ 2) * (B * (R - A * p)) * p +
        (B * (R - A * p)) ^ 2 * s := by rw [hV, ← hα', ← hβ']; ring
    have key2 : R ^ 2 * (c ^ 2 - V) = B * (c ^ 2 - B * s) * (R - A * p) ^ 2 := by
      linear_combination (-1) * hRV - c ^ 2 * R ^ 2 * hA2 + c ^ 2 * A ^ 2 * hR2 + c ^ 2 * A ^ 2 * hQ
    have hRe : 0 < R - A * p := by linarith
    have hce : 0 < c ^ 2 - e := by
      have h1 : 0 < R * (c ^ 2 - e) := by rw [key1]; positivity
      exact pos_of_mul_pos_right h1 hR0.le
    have hn0 : n ≠ 0 := by intro h; rw [h] at hn; linarith
    by_cases hu0 : u = 0
    · have hs' : s = 0 := by rw [hs, hu0]; simp [dot3]
      have hp' : p = 0 := by rw [hp, hu0]; simp [dot3]
      rw [comovingVelocity, if_pos hu0, hVd]
      rw [hs', hp'] at key2
      rw [hs'] at hnA
      have h1 : c ^ 2 - V = B * c ^ 2 := by
        have : R ^ 2 * (c ^ 2 - V) = R ^ 2 * (B * c ^ 2) := by rw [key2]; ring
        exact mul_left_cancel₀ (by positivity) this
      rw [eq_div_iff (by positivity)]
      linear_combination (-n ^ 2) * h1 - n ^ 2 * c ^ 2 * hA2 + hnA
    · rw [comovingVelocity, if_neg hu0, x6r_dot_smul_left, x6r_dot_smul_right, hed]
      have hsp : 0 < s := by rw [hs]; exact x6r_dot_pos u hu0
      generalize hγd : lorentzFactor c u = γ at hγ2 hγ0 ⊢
      have hγ' : γ ^ 2 * (c ^ 2 - s) = c ^ 2 := by rw [hγ2, div_mul_cancel₀ _ hcs.ne']
      have hw := x6r_hw v u ((γ - 1) * (e - s) / s)
      generalize hτ : (γ - 1) * (e - s) / s - 1 = τ at hw
      have hτs : τ * s = (γ - 1) * e - γ * s := by
        rw [← hτ, sub_mul, div_mul_cancel₀ _ hsp.ne']; ring
      rw [← hs, hw]
      simp only [x6r_dot_add_left, x6r_dot_add_right, x6r_dot_smul_left, x6r_dot_smul_right]
      rw [x6r_dot_comm v u, hed, hVd, ← hs]
      generalize hWd : V + τ * e + τ * (e + τ * s) = W
      have hsW : s * W = s * V + 2 * e * ((γ - 1) * e - γ * s) + ((γ - 1) * e - γ * s) ^ 2 := by
        rw [← hWd, ← hτs]; ring
      have hcW : s * (c ^ 2 * W - γ ^ 2 * (V * (c ^ 2 - s) + c ^ 2 * s + e ^ 2 - 2 * c ^ 2 * e)) = 0 := by
        linear_combination c ^ 2 * hsW + (e ^ 2 - s * V) * hγ'
      have hcW' : c ^ 2 * W = γ ^ 2 * (V * (c ^ 2 - s) + c ^ 2 * s + e ^ 2 - 2 * c ^ 2 * e) := by
        have := (mul_eq_zero.1 hcW).resolve_left hsp.ne'
        linear_combination this
      have hZ : R ^ 2 * ((n ^ 2 - 1) * (c ^ 2 - e) ^ 2 - n ^ 2 * (c ^ 2 - s) * (c ^ 2 - V)) = 0 := by
        linear_combination (n ^ 2 - 1) * (R * (c ^ 2 - e) + (c ^ 2 - B * s) * (R - A * p)) * key1 -
          n ^ 2 * (c ^ 2 - s) * key2 + (c ^ 2 - B * s) * (R - A * p) ^ 2 * hnA -
          n ^ 2 * c ^ 2 * (c ^ 2 - B * s) * (R - A * p) ^ 2 * hA2
      have hZ' : (n ^ 2 - 1) * (c ^ 2 - e) ^ 2 - n ^ 2 * (c ^ 2 - s) * (c ^ 2 - V) = 0 :=
        (mul_eq_zero.1 hZ).resolve_left (by positivity)
      exact x6r_final c n γ e s V W hc2 hγ0 hce hn0 hcW' hZ'
  · rw [hζ, hdir, hr, hH]; field_simp
  · rw [hζ, hderiv, hdir, hr, hvel k hpos, ← hqd, ← hp, ← hQ, ← hR, x6r_cross, x6r_dot_smul_left,
      x6r_dot_smul_left, x6r_dot_smul_right, ← hqd, x6r_dot_comm k u, ← hp]
    funext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination (A * c ^ 2 * k j + B * (R - A * p) * u j) * hlen - k j * A * hR2 - k j * A * hQ
  · intro a ha
    have hak1 : dot3 u (a • k) = a * p := by rw [x6r_dot_smul_right, hp]
    have hak2 : c ^ 2 * dot3 (a • k) (a • k) - B * dot3 u (a • k) ^ 2 = a ^ 2 * Q := by
      rw [hak1, x6r_dot_smul_right, x6r_dot_smul_left, ← hqd, hQ]; ring
    have hRa : Real.sqrt (c ^ 2 * dot3 (a • k) (a • k) - B * dot3 u (a • k) ^ 2) = a * R := by
      rw [hak2, Real.sqrt_mul (by positivity), Real.sqrt_sq ha.le, hR]
    refine ⟨?_, ?_⟩
    · rw [hHk, hRa, hak1, hH]; ring
    · have hpos' : 0 < c ^ 2 * dot3 (a • k) (a • k) - B * dot3 u (a • k) ^ 2 := by
        rw [hak2]; positivity
      have hpos : 0 < c ^ 2 * dot3 k k - B * dot3 u k ^ 2 := by rw [← hqd, ← hp, ← hQ]; exact hQ0
      rw [hvel _ hpos', hvel _ hpos, hRa, hak1, ← hp, ← hqd, ← hQ, ← hR]
      funext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
