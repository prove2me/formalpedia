-- Prove2me | solution 1 for PereiraGuimaraesElko.euler_lagrange_eqs_A14_A17
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:33:26.627068+00:00
-- url     : https://prove2.me/submissions/b2ec187e-fbc8-4a02-b8c7-cb0b04333a3c

import Mathlib

namespace ElkoEL

lemma deriv_cubic (g : ℝ → ℝ) (c1 c2 c3 : ℝ) (hg : ∀ w, g w = g 0 + c1 * w + c2 * w ^ 2 + c3 * w ^ 3)
    (x : ℝ) : deriv g x = c1 + 2 * c2 * x + 3 * c3 * x ^ 2 := by
  rw [show g = fun w => g 0 + c1 * w + c2 * w ^ 2 + c3 * w ^ 3 from funext hg]
  have := ((((hasDerivAt_id x).const_mul c1).const_add (g 0)).add
    ((hasDerivAt_pow 2 x).const_mul c2)).add ((hasDerivAt_pow 3 x).const_mul c3)
  refine this.deriv.trans ?_; simp; ring

lemma deriv_potential (g V : ℝ → ℝ) (hV : Differentiable ℝ V) (c0 c1 c2 : ℝ)
    (hg : ∀ u, g u = c0 + c1 * u ^ 2 + c2 * V u) (x : ℝ) :
    deriv g x = 2 * c1 * x + c2 * deriv V x := by
  rw [show g = fun u => c0 + c1 * u ^ 2 + c2 * V u from funext hg]
  have := (((hasDerivAt_pow 2 x).const_mul c1).const_add c0).add ((hV x).hasDerivAt.const_mul c2)
  refine this.deriv.trans ?_; simp; ring

lemma deriv_N (g : ℝ → ℝ) (S T : ℝ) (hg : ∀ N, g N = -(1 / N) * S - N * T) :
    deriv g 1 = S - T := by
  rw [show g = fun N => -(1 / N) * S - N * T from funext hg]
  have h1 : HasDerivAt (fun N : ℝ => 1 / N) (-(1 : ℝ) / 1 ^ 2) 1 := by
    have := (hasDerivAt_inv (x := (1 : ℝ)) one_ne_zero)
    simpa [one_div] using this
  have := ((h1.neg).mul_const S).sub ((hasDerivAt_id (1 : ℝ)).mul_const T)
  refine this.deriv.trans ?_
  simp

end ElkoEL

theorem solution (κ : ℝ) (hκ : κ ≠ 0) (V : ℝ → ℝ) (hV : Differentiable ℝ V)
    (L : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hL : ∀ N a ad Φ Φd h f, L N a ad Φ Φd h f =
      -(1 / N) * (3 * a * ad ^ 2 / κ ^ 2 - 3 * a ^ 3 * h ^ 2 / κ ^ 2 - 1 / 2 * a ^ 3 * Φd ^ 2
        - 3 / 8 * a * (ad + a * h) ^ 2 * Φ ^ 2)
      - N * (3 * a ^ 3 * f ^ 2 / κ ^ 2 + 3 / 8 * a ^ 3 * f ^ 2 * Φ ^ 2 + a ^ 3 * V Φ))
    (I : Set ℝ) (hI : IsOpen I) (a Φ h f : ℝ → ℝ)
    (ha : ∀ t ∈ I, 0 < a t)
    (ha1 : ∀ t ∈ I, DifferentiableAt ℝ a t) (ha2 : ∀ t ∈ I, DifferentiableAt ℝ (deriv a) t)
    (hΦ1 : ∀ t ∈ I, DifferentiableAt ℝ Φ t) (hΦ2 : ∀ t ∈ I, DifferentiableAt ℝ (deriv Φ) t)
    (hh : ∀ t ∈ I, DifferentiableAt ℝ h t)
    (EL_N : ∀ t ∈ I,
      deriv (fun N => L N (a t) (deriv a t) (Φ t) (deriv Φ t) (h t) (f t)) 1 = 0)
    (EL_a : ∀ t ∈ I,
      deriv (fun s => deriv (fun v => L 1 (a s) v (Φ s) (deriv Φ s) (h s) (f s)) (deriv a s)) t
        - deriv (fun u => L 1 u (deriv a t) (Φ t) (deriv Φ t) (h t) (f t)) (a t) = 0)
    (EL_Φ : ∀ t ∈ I,
      deriv (fun s => deriv (fun w => L 1 (a s) (deriv a s) (Φ s) w (h s) (f s)) (deriv Φ s)) t
        - deriv (fun u => L 1 (a t) (deriv a t) u (deriv Φ t) (h t) (f t)) (Φ t) = 0)
    (EL_h : ∀ t ∈ I,
      deriv (fun w => L 1 (a t) (deriv a t) (Φ t) (deriv Φ t) w (f t)) (h t) = 0)
    (EL_f : ∀ t ∈ I,
      deriv (fun w => L 1 (a t) (deriv a t) (Φ t) (deriv Φ t) (h t) w) (f t) = 0) :
    let H : ℝ → ℝ := fun t => deriv a t / a t
    ∀ t ∈ I,
      3 * H t ^ 2 = κ ^ 2 * (deriv Φ t ^ 2 / 2 + V (Φ t) + 3 / 8 * H t ^ 2 * Φ t ^ 2
          + 3 / 4 * H t * h t * Φ t ^ 2)
        + 3 * (1 + 1 / 8 * κ ^ 2 * Φ t ^ 2) * h t ^ 2
        + 3 * (1 + 1 / 8 * κ ^ 2 * Φ t ^ 2) * f t ^ 2 ∧
      -2 * deriv H t - 3 * H t ^ 2 = κ ^ 2 * (deriv Φ t ^ 2 / 2 - V (Φ t)
          - 3 / 8 * H t ^ 2 * Φ t ^ 2 - 1 / 4 * deriv (fun s => (H s + h s) * Φ s ^ 2) t)
        + 3 * (1 + 1 / 8 * κ ^ 2 * Φ t ^ 2) * h t ^ 2
        - 3 * (1 + 1 / 8 * κ ^ 2 * Φ t ^ 2) * f t ^ 2 ∧
      deriv (deriv Φ) t + 3 * H t * deriv Φ t + deriv V (Φ t)
        - 3 / 4 * ((H t + h t) ^ 2 - f t ^ 2) * Φ t = 0 ∧
      h t = -(1 / 8) * (κ ^ 2 * Φ t ^ 2 / (1 + κ ^ 2 * Φ t ^ 2 / 8)) * (deriv a t / a t) ∧
      f t = 0
  := by
  intro H t ht
  have hκ2 : κ ^ 2 ≠ 0 := pow_ne_zero 2 hκ
  have hA : 0 < a t := ha t ht
  have hA0 : a t ≠ 0 := hA.ne'
  have hD : 0 < 1 + κ ^ 2 * Φ t ^ 2 / 8 := by positivity
  -- EL_N
  have hN := EL_N t ht
  rw [ElkoEL.deriv_N _
    (3 * a t * deriv a t ^ 2 / κ ^ 2 - 3 * a t ^ 3 * h t ^ 2 / κ ^ 2 - 1 / 2 * a t ^ 3 * deriv Φ t ^ 2
        - 3 / 8 * a t * (deriv a t + a t * h t) ^ 2 * Φ t ^ 2)
    (3 * a t ^ 3 * f t ^ 2 / κ ^ 2 + 3 / 8 * a t ^ 3 * f t ^ 2 * Φ t ^ 2 + a t ^ 3 * V (Φ t))
    (fun N => by rw [hL])] at hN
  -- EL_h
  have hEh := EL_h t ht
  rw [ElkoEL.deriv_cubic _ (3 / 4 * a t ^ 2 * deriv a t * Φ t ^ 2)
    (3 * a t ^ 3 / κ ^ 2 + 3 / 8 * a t ^ 3 * Φ t ^ 2) 0 (fun w => by simp only [hL]; ring)] at hEh
  -- EL_f
  have hf := EL_f t ht
  rw [ElkoEL.deriv_cubic _ 0
    (-(3 * a t ^ 3 / κ ^ 2 + 3 / 8 * a t ^ 3 * Φ t ^ 2)) 0 (fun w => by simp only [hL]; ring)] at hf
  -- EL_Φ
  have hP := EL_Φ t ht
  have innerΦ : (fun s => deriv (fun w => L 1 (a s) (deriv a s) (Φ s) w (h s) (f s)) (deriv Φ s))
      = fun s => a s ^ 3 * deriv Φ s := by
    funext s
    rw [ElkoEL.deriv_cubic _ 0 (1 / 2 * a s ^ 3) 0 (fun w => by simp only [hL]; ring)]
    ring
  have hPo : HasDerivAt (fun s => a s ^ 3 * deriv Φ s)
      (3 * a t ^ 2 * deriv a t * deriv Φ t + a t ^ 3 * deriv (deriv Φ) t) t := by
    have := ((ha1 t ht).hasDerivAt.pow 3).mul (hΦ2 t ht).hasDerivAt
    refine this.congr_deriv ?_; push_cast; simp only [Pi.pow_apply]
  rw [innerΦ, hPo.deriv, ElkoEL.deriv_potential (fun u => L 1 (a t) (deriv a t) u (deriv Φ t) (h t) (f t)) V hV
    (-(3 * a t * deriv a t ^ 2 / κ ^ 2 - 3 * a t ^ 3 * h t ^ 2 / κ ^ 2 - 1 / 2 * a t ^ 3 * deriv Φ t ^ 2)
      - 3 * a t ^ 3 * f t ^ 2 / κ ^ 2)
    (3 / 8 * a t * (deriv a t + a t * h t) ^ 2 - 3 / 8 * a t ^ 3 * f t ^ 2) (-(a t ^ 3))
    (fun u => by simp only [hL]; ring)] at hP
  -- EL_a
  have hAe := EL_a t ht
  have innerA : (fun s => deriv (fun v => L 1 (a s) v (Φ s) (deriv Φ s) (h s) (f s)) (deriv a s))
      = fun s => 3 / 4 * a s ^ 2 * h s * Φ s ^ 2
          + 2 * (-3 * a s / κ ^ 2 + 3 / 8 * a s * Φ s ^ 2) * deriv a s := by
    funext s
    rw [ElkoEL.deriv_cubic _ (3 / 4 * a s ^ 2 * h s * Φ s ^ 2)
      (-3 * a s / κ ^ 2 + 3 / 8 * a s * Φ s ^ 2) 0 (fun w => by simp only [hL]; ring)]
    ring
  have hAo : HasDerivAt (fun s => 3 / 4 * a s ^ 2 * h s * Φ s ^ 2
          + 2 * (-3 * a s / κ ^ 2 + 3 / 8 * a s * Φ s ^ 2) * deriv a s)
      (3 / 4 * (2 * a t * deriv a t * h t * Φ t ^ 2 + a t ^ 2 * deriv h t * Φ t ^ 2
          + a t ^ 2 * h t * (2 * Φ t * deriv Φ t))
        + 2 * ((-3 * deriv a t / κ ^ 2 + 3 / 8 * (deriv a t * Φ t ^ 2 + a t * (2 * Φ t * deriv Φ t)))
            * deriv a t + (-3 * a t / κ ^ 2 + 3 / 8 * a t * Φ t ^ 2) * deriv (deriv a) t)) t := by
    have a1 := (ha1 t ht).hasDerivAt
    have a2 := (ha2 t ht).hasDerivAt
    have p1 := (hΦ1 t ht).hasDerivAt
    have h1 := (hh t ht).hasDerivAt
    have := ((((a1.pow 2).const_mul (3 / 4)).mul h1).mul (p1.pow 2)).add
      ((((a1.div_const (κ ^ 2)).const_mul (-3)).add ((a1.mul (p1.pow 2)).const_mul (3 / 8))).const_mul 2
        |>.mul a2)
    refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    · simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply]; push_cast; ring
    · simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply]; ring
  rw [innerA, hAo.deriv, ElkoEL.deriv_cubic (fun u => L 1 u (deriv a t) (Φ t) (deriv Φ t) (h t) (f t))
    (-3 * deriv a t ^ 2 / κ ^ 2 + 3 / 8 * deriv a t ^ 2 * Φ t ^ 2)
    (3 / 4 * deriv a t * h t * Φ t ^ 2)
    (3 * h t ^ 2 / κ ^ 2 + 1 / 2 * deriv Φ t ^ 2 + 3 / 8 * h t ^ 2 * Φ t ^ 2 - 3 * f t ^ 2 / κ ^ 2
      - 3 / 8 * f t ^ 2 * Φ t ^ 2 - V (Φ t))
    (fun w => by simp only [hL]; ring)] at hAe
  -- H and X
  have hHd : HasDerivAt H ((deriv (deriv a) t * a t - deriv a t * deriv a t) / a t ^ 2) t :=
    (ha2 t ht).hasDerivAt.div (ha1 t ht).hasDerivAt hA0
  have hX : HasDerivAt (fun s => (H s + h s) * Φ s ^ 2)
      ((((deriv (deriv a) t * a t - deriv a t * deriv a t) / a t ^ 2) + deriv h t) * Φ t ^ 2
        + (H t + h t) * (2 * Φ t * deriv Φ t)) t := by
    have := (hHd.add (hh t ht).hasDerivAt).mul ((hΦ1 t ht).hasDerivAt.pow 2)
    refine this.congr_deriv ?_; push_cast; simp only [Pi.pow_apply, Pi.add_apply]; ring
  have hHt : H t = deriv a t / a t := rfl
  rw [hHd.deriv, hX.deriv, hHt]
  have hD0 : 1 + κ ^ 2 * Φ t ^ 2 / 8 ≠ 0 := hD.ne'
  generalize a t = A at *
  generalize deriv a t = Ad at *
  generalize deriv (deriv a) t = Add at *
  generalize Φ t = P at *
  generalize deriv Φ t = Pd at *
  generalize deriv (deriv Φ) t = Pdd at *
  generalize h t = hv at *
  generalize deriv h t = hd at *
  generalize f t = F at *
  generalize V P = Vp at *
  generalize deriv V P = dV at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have e : 3 * (Ad / A) ^ 2 - (κ ^ 2 * (Pd ^ 2 / 2 + Vp + 3 / 8 * (Ad / A) ^ 2 * P ^ 2 +
              3 / 4 * (Ad / A) * hv * P ^ 2) + 3 * (1 + 1 / 8 * κ ^ 2 * P ^ 2) * hv ^ 2 +
            3 * (1 + 1 / 8 * κ ^ 2 * P ^ 2) * F ^ 2) =
        κ ^ 2 / A ^ 3 * (3 * A * Ad ^ 2 / κ ^ 2 - 3 * A ^ 3 * hv ^ 2 / κ ^ 2 - 1 / 2 * A ^ 3 * Pd ^ 2 -
          3 / 8 * A * (Ad + A * hv) ^ 2 * P ^ 2 -
          (3 * A ^ 3 * F ^ 2 / κ ^ 2 + 3 / 8 * A ^ 3 * F ^ 2 * P ^ 2 + A ^ 3 * Vp)) := by
      field_simp; ring
    rw [hN, mul_zero] at e; linarith
  · have e : -2 * ((Add * A - Ad * Ad) / A ^ 2) - 3 * (Ad / A) ^ 2 -
        (κ ^ 2 * (Pd ^ 2 / 2 - Vp - 3 / 8 * (Ad / A) ^ 2 * P ^ 2 -
              1 / 4 * (((Add * A - Ad * Ad) / A ^ 2 + hd) * P ^ 2 + (Ad / A + hv) * (2 * P * Pd))) +
            3 * (1 + 1 / 8 * κ ^ 2 * P ^ 2) * hv ^ 2 - 3 * (1 + 1 / 8 * κ ^ 2 * P ^ 2) * F ^ 2) =
        κ ^ 2 / (3 * A ^ 2) * (3 / 4 * (2 * A * Ad * hv * P ^ 2 + A ^ 2 * hd * P ^ 2 +
            A ^ 2 * hv * (2 * P * Pd)) +
          2 * ((-3 * Ad / κ ^ 2 + 3 / 8 * (Ad * P ^ 2 + A * (2 * P * Pd))) * Ad +
            (-3 * A / κ ^ 2 + 3 / 8 * A * P ^ 2) * Add) -
          (-3 * Ad ^ 2 / κ ^ 2 + 3 / 8 * Ad ^ 2 * P ^ 2 + 2 * (3 / 4 * Ad * hv * P ^ 2) * A +
            3 * (3 * hv ^ 2 / κ ^ 2 + 1 / 2 * Pd ^ 2 + 3 / 8 * hv ^ 2 * P ^ 2 - 3 * F ^ 2 / κ ^ 2 -
              3 / 8 * F ^ 2 * P ^ 2 - Vp) * A ^ 2)) := by
      field_simp; ring
    rw [hAe, mul_zero] at e; linarith
  · have e : Pdd + 3 * (Ad / A) * Pd + dV - 3 / 4 * ((Ad / A + hv) ^ 2 - F ^ 2) * P =
        1 / A ^ 3 * (3 * A ^ 2 * Ad * Pd + A ^ 3 * Pdd -
          (2 * (3 / 8 * A * (Ad + A * hv) ^ 2 - 3 / 8 * A ^ 3 * F ^ 2) * P + -A ^ 3 * dV)) := by
      field_simp; ring
    rw [hP, mul_zero] at e; exact e
  · have e : hv - -(1 / 8) * (κ ^ 2 * P ^ 2 / (1 + κ ^ 2 * P ^ 2 / 8)) * (Ad / A) =
        κ ^ 2 / (6 * A ^ 3 * (1 + κ ^ 2 * P ^ 2 / 8)) * (3 / 4 * A ^ 2 * Ad * P ^ 2 +
          2 * (3 * A ^ 3 / κ ^ 2 + 3 / 8 * A ^ 3 * P ^ 2) * hv + 3 * 0 * hv ^ 2) := by
      field_simp; ring
    rw [hEh, mul_zero] at e; linarith
  · have e : F = -κ ^ 2 / (6 * A ^ 3 * (1 + κ ^ 2 * P ^ 2 / 8)) *
        (0 + 2 * -(3 * A ^ 3 / κ ^ 2 + 3 / 8 * A ^ 3 * P ^ 2) * F + 3 * 0 * F ^ 2) := by
      field_simp; ring
    rw [hf, mul_zero] at e; exact e
