-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap50repair.P01.krein_sign_rescaling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:46:07.12199+00:00
-- url     : https://prove2.me/submissions/89913be8-9c68-4a94-a50e-0bed324ec296

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01
noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius ComplexConjugate

open QAlgorithms.Papers.Independent.Gap50repair.P01
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic canonicalJ)

namespace X4CZE

attribute [local instance] Classical.propDecidable

local notation "L" => (Sum.inl (0 : Fin 1) : Coord 1)
local notation "R" => (Sum.inr (0 : Fin 1) : Coord 1)

lemma omegaR_two (v w : Coord 1 → ℝ) : omegaR v w = v L * w R - v R * w L := by
  simp [omegaR]

/-- Component equations of an eigenvector `v - i w`. -/
lemma comps (A : GroupedRealMatrix 1) (z : ℂ) (v w : Coord 1 → ℝ)
    (hev : (complexify A).mulVec (fun i => (v i : ℂ)-Complex.I*(w i : ℂ)) =
      z • (fun i => (v i : ℂ)-Complex.I*(w i : ℂ))) :
    (A L L : ℂ) * (v L - Complex.I * w L) + (A L R : ℂ) * (v R - Complex.I * w R) =
        z * (v L - Complex.I * w L) ∧
    (A R L : ℂ) * (v L - Complex.I * w L) + (A R R : ℂ) * (v R - Complex.I * w R) =
        z * (v R - Complex.I * w R) := by
  have e1 := congrFun hev L
  have e2 := congrFun hev R
  simp [Matrix.mulVec, dotProduct, complexify, Fintype.sum_sum_type] at e1 e2
  exact ⟨e1, e2⟩

lemma conj_comps (A : GroupedRealMatrix 1) (z : ℂ) (v w : Coord 1 → ℝ)
    (h : (A L L : ℂ) * (v L - Complex.I * w L) + (A L R : ℂ) * (v R - Complex.I * w R) =
        z * (v L - Complex.I * w L) ∧
    (A R L : ℂ) * (v L - Complex.I * w L) + (A R R : ℂ) * (v R - Complex.I * w R) =
        z * (v R - Complex.I * w R)) :
    (A L L : ℂ) * (v L + Complex.I * w L) + (A L R : ℂ) * (v R + Complex.I * w R) =
        conj z * (v L + Complex.I * w L) ∧
    (A R L : ℂ) * (v L + Complex.I * w L) + (A R R : ℂ) * (v R + Complex.I * w R) =
        conj z * (v R + Complex.I * w R) := by
  obtain ⟨h1, h2⟩ := h
  have c1 := congrArg conj h1
  have c2 := congrArg conj h2
  simp [map_add, map_mul, map_sub, Complex.conj_ofReal, Complex.conj_I] at c1 c2
  exact ⟨by linear_combination c1, by linear_combination c2⟩

lemma u_zero {v w : Coord 1 → ℝ} (h1 : v L = 0) (h2 : w L = 0) (h3 : v R = 0) (h4 : w R = 0) :
    (fun i => (v i : ℂ)-Complex.I*(w i : ℂ)) = 0 := by
  funext i
  rcases i with i | i <;> obtain rfl := Fin.fin_one_eq_zero i <;> simp [*]

lemma normsq_zero {a b : ℝ} (h : ((a : ℂ) - Complex.I * b) * ((a : ℂ) + Complex.I * b) = 0) :
    a = 0 ∧ b = 0 := by
  have : ((a^2 + b^2 : ℝ) : ℂ) = 0 := by
    push_cast; linear_combination h + b^2 * Complex.I_sq
  have h' : a^2 + b^2 = 0 := by exact_mod_cast this
  constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]

lemma im_ne {z : ℂ} (hz : z.im ≠ 0) : z - conj z ≠ 0 := by
  intro h
  apply hz
  have := congrArg Complex.im h
  simp at this
  linarith

/-- The omega value of an eigenvector for a nonreal eigenvalue is nonzero. -/
lemma omega_ne (A : GroupedRealMatrix 1) (z : ℂ) (hzr : z.im ≠ 0) (v w : Coord 1 → ℝ)
    (he : (fun i => (v i : ℂ)-Complex.I*(w i : ℂ)) ≠ 0)
    (hev : (complexify A).mulVec (fun i => (v i : ℂ)-Complex.I*(w i : ℂ)) =
      z • (fun i => (v i : ℂ)-Complex.I*(w i : ℂ))) : omegaR v w ≠ 0 := by
  intro hD
  rw [omegaR_two] at hD
  have hDc : ((v L : ℂ) * w R - v R * w L) = 0 := by exact_mod_cast hD
  obtain ⟨h1, h2⟩ := comps A z v w hev
  obtain ⟨c1, c2⟩ := conj_comps A z v w ⟨h1, h2⟩
  have hz := im_ne hzr
  have p0 : (z - conj z) * (((v L : ℂ) - Complex.I * w L) * ((v L : ℂ) + Complex.I * w L)) = 0 := by
    linear_combination -((v L : ℂ) + Complex.I * w L) * h1 + ((v L : ℂ) - Complex.I * w L) * c1
      - 2 * Complex.I * (A L R : ℂ) * hDc
  have q0 : (z - conj z) * (((v R : ℂ) - Complex.I * w R) * ((v R : ℂ) + Complex.I * w R)) = 0 := by
    linear_combination -((v R : ℂ) + Complex.I * w R) * h2 + ((v R : ℂ) - Complex.I * w R) * c2
      + 2 * Complex.I * (A R L : ℂ) * hDc
  obtain ⟨a1, a2⟩ := normsq_zero ((mul_eq_zero.1 p0).resolve_left hz)
  obtain ⟨b1, b2⟩ := normsq_zero ((mul_eq_zero.1 q0).resolve_left hz)
  exact he (u_zero a1 a2 b1 b2)

theorem main (A : GroupedRealMatrix 1) (hA : IsSymplectic A)
    (z : ℂ) (hz : ‖z‖ = 1) (hzr : z.im ≠ 0) (v w : Coord 1 → ℝ)
    (he : (fun i => (v i : ℂ)-Complex.I*(w i : ℂ)) ≠ 0)
    (hev : (complexify A).mulVec (fun i => (v i : ℂ)-Complex.I*(w i : ℂ)) =
      z • (fun i => (v i : ℂ)-Complex.I*(w i : ℂ))) :
    omegaR v w ≠ 0 ∧
    (∀ a b : ℝ, 0 < a^2+b^2 →
      omegaR (a • v+b • w) ((-b) • v+a • w) = (a^2+b^2)*omegaR v w ∧
      Real.sign (omegaR (a • v+b • w) ((-b) • v+a • w)) = Real.sign (omegaR v w)) ∧
    (∀ v2 w2 : Coord 1 → ℝ,
      (fun i => (v2 i : ℂ)-Complex.I*(w2 i : ℂ)) ≠ 0 →
      (complexify A).mulVec (fun i => (v2 i : ℂ)-Complex.I*(w2 i : ℂ)) =
        z • (fun i => (v2 i : ℂ)-Complex.I*(w2 i : ℂ)) →
      Real.sign (omegaR v2 w2) = Real.sign (omegaR v w)) ∧
    (complexify A).mulVec (fun i => (v i : ℂ)+Complex.I*(w i : ℂ)) =
      (star z) • (fun i => (v i : ℂ)+Complex.I*(w i : ℂ)) ∧
    omegaR v (-w) = -omegaR v w ∧
    omegaC (fun i => (v i : ℂ)-Complex.I*(w i : ℂ))
      (fun i => (v i : ℂ)+Complex.I*(w i : ℂ)) = 2*Complex.I*(omegaR v w : ℂ) := by
  have hD := omega_ne A z hzr v w he hev
  refine ⟨hD, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have e : omegaR (a • v+b • w) ((-b) • v+a • w) = (a^2+b^2)*omegaR v w := by
      simp only [omegaR_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    refine ⟨e, ?_⟩
    rw [e]
    rcases lt_trichotomy (omegaR v w) 0 with h | h | h
    · rw [Real.sign_of_neg h, Real.sign_of_neg (mul_neg_of_pos_of_neg hab h)]
    · rw [h, mul_zero]
    · rw [Real.sign_of_pos h, Real.sign_of_pos (mul_pos hab h)]
  · intro v2 w2 he2 hev2
    have hD2 := omega_ne A z hzr v2 w2 he2 hev2
    obtain ⟨h1, h2⟩ := comps A z v w hev
    obtain ⟨k1, k2⟩ := comps A z v2 w2 hev2
    obtain ⟨c1, c2⟩ := conj_comps A z v w ⟨h1, h2⟩
    obtain ⟨d1, d2⟩ := conj_comps A z v2 w2 ⟨k1, k2⟩
    set p : ℂ := (v L : ℂ) - Complex.I * w L
    set q : ℂ := (v R : ℂ) - Complex.I * w R
    set pb : ℂ := (v L : ℂ) + Complex.I * w L
    set qb : ℂ := (v R : ℂ) + Complex.I * w R
    set p2 : ℂ := (v2 L : ℂ) - Complex.I * w2 L
    set q2 : ℂ := (v2 R : ℂ) - Complex.I * w2 R
    set pb2 : ℂ := (v2 L : ℂ) + Complex.I * w2 L
    set qb2 : ℂ := (v2 R : ℂ) + Complex.I * w2 R
    have haz : (A L L : ℂ) - z ≠ 0 := by
      intro h; apply hzr; have := congrArg Complex.im h; simp at this <;> linarith
    have hazb : (A L L : ℂ) - conj z ≠ 0 := by
      intro h; apply hzr; have := congrArg Complex.im h; simp at this <;> linarith
    have hpq : p * q2 - p2 * q = 0 := by
      have : ((A L L : ℂ) - z) * (p * q2 - p2 * q) = 0 := by
        linear_combination q2 * h1 - q * k1
      exact (mul_eq_zero.1 this).resolve_left haz
    have hpqb : pb * qb2 - pb2 * qb = 0 := by
      have : ((A L L : ℂ) - conj z) * (pb * qb2 - pb2 * qb) = 0 := by
        linear_combination qb2 * c1 - qb * d1
      exact (mul_eq_zero.1 this).resolve_left hazb
    have X : p * qb - q * pb = 2 * Complex.I * (omegaR v w : ℂ) := by
      rw [omegaR_two]; push_cast; simp only [p, q, pb, qb]; (ring_nf <;> (try rw [Complex.I_sq]) <;> ring_nf)
    have X2 : p2 * qb2 - q2 * pb2 = 2 * Complex.I * (omegaR v2 w2 : ℂ) := by
      rw [omegaR_two]; push_cast; simp only [p2, q2, pb2, qb2]; (ring_nf <;> (try rw [Complex.I_sq]) <;> ring_nf)
    have i1 : (p * pb) * (p2 * qb2 - q2 * pb2) = (p2 * pb2) * (p * qb - q * pb) := by
      linear_combination (p*p2) * hpqb - (pb*pb2) * hpq
    have i2 : (q * qb) * (p2 * qb2 - q2 * pb2) = (q2 * qb2) * (p * qb - q * pb) := by
      linear_combination q*q2*hpqb - qb*qb2*hpq
    have np : p * pb = ((v L ^ 2 + w L ^ 2 : ℝ) : ℂ) := by
      push_cast; simp only [p, pb]; (ring_nf <;> (try rw [Complex.I_sq]) <;> ring_nf)
    have nq : q * qb = ((v R ^ 2 + w R ^ 2 : ℝ) : ℂ) := by
      push_cast; simp only [q, qb]; (ring_nf <;> (try rw [Complex.I_sq]) <;> ring_nf)
    have np2 : p2 * pb2 = ((v2 L ^ 2 + w2 L ^ 2 : ℝ) : ℂ) := by
      push_cast; simp only [p2, pb2]; (ring_nf <;> (try rw [Complex.I_sq]) <;> ring_nf)
    have nq2 : q2 * qb2 = ((v2 R ^ 2 + w2 R ^ 2 : ℝ) : ℂ) := by
      push_cast; simp only [q2, qb2]; (ring_nf <;> (try rw [Complex.I_sq]) <;> ring_nf)
    have key : ((v L ^ 2 + w L ^ 2 + (v R ^ 2 + w R ^ 2)) * omegaR v2 w2 : ℝ) =
        (v2 L ^ 2 + w2 L ^ 2 + (v2 R ^ 2 + w2 R ^ 2)) * omegaR v w := by
      have hc : (p*pb + q*qb) * (2*Complex.I*(omegaR v2 w2:ℂ)) =
          (p2*pb2 + q2*qb2) * (2*Complex.I*(omegaR v w : ℂ)) := by
        rw [← X, ← X2]; linear_combination i1 + i2
      rw [np, nq, np2, nq2] at hc
      have hc' : (((v L ^ 2 + w L ^ 2 + (v R ^ 2 + w R ^ 2)) * omegaR v2 w2 : ℝ) : ℂ) * (2 * Complex.I) =
          (((v2 L ^ 2 + w2 L ^ 2 + (v2 R ^ 2 + w2 R ^ 2)) * omegaR v w : ℝ) : ℂ) * (2 * Complex.I) := by
        push_cast; push_cast at hc; linear_combination hc
      have h2I : (2 * Complex.I) ≠ 0 := by simp
      exact_mod_cast mul_right_cancel₀ h2I hc'
    have S : 0 < v L ^ 2 + w L ^ 2 + (v R ^ 2 + w R ^ 2) := by
      by_contra hS
      apply he
      apply u_zero <;> nlinarith [sq_nonneg (v L), sq_nonneg (w L), sq_nonneg (v R), sq_nonneg (w R)]
    have S2 : 0 < v2 L ^ 2 + w2 L ^ 2 + (v2 R ^ 2 + w2 R ^ 2) := by
      by_contra hS
      apply he2
      apply u_zero <;> nlinarith [sq_nonneg (v2 L), sq_nonneg (w2 L), sq_nonneg (v2 R), sq_nonneg (w2 R)]
    rcases lt_or_gt_of_ne hD with h | h
    · have : omegaR v2 w2 < 0 := by
        by_contra hc; push_neg at hc; nlinarith [mul_nonneg S.le hc, mul_pos S2 (neg_pos.2 h)]
      rw [Real.sign_of_neg h, Real.sign_of_neg this]
    · have : 0 < omegaR v2 w2 := by
        by_contra hc; push_neg at hc; nlinarith [mul_nonneg S.le (neg_nonneg.2 hc), mul_pos S2 h]
      rw [Real.sign_of_pos h, Real.sign_of_pos this]
  · obtain ⟨c1, c2⟩ := conj_comps A z v w (comps A z v w hev)
    funext i
    rcases i with i | i <;> obtain rfl := Fin.fin_one_eq_zero i <;>
      simp [Matrix.mulVec, dotProduct, complexify, Fintype.sum_sum_type]
    · linear_combination c1
    · linear_combination c2
  · simp only [omegaR_two, Pi.neg_apply]; ring
  · simp [omegaC, omegaR_two]
    (ring_nf <;> (try rw [Complex.I_sq]) <;> ring_nf)

end X4CZE

theorem solution (A : GroupedRealMatrix 1) (hA : IsSymplectic A)
    (z : ℂ) (hz : ‖z‖ = 1) (hzr : z.im ≠ 0) (v w : Coord 1 → ℝ)
    (he : (fun i => (v i : ℂ)-Complex.I*(w i : ℂ)) ≠ 0)
    (hev : (complexify A).mulVec (fun i => (v i : ℂ)-Complex.I*(w i : ℂ)) =
      z • (fun i => (v i : ℂ)-Complex.I*(w i : ℂ))) :
    omegaR v w ≠ 0 ∧
    (∀ a b : ℝ, 0 < a^2+b^2 →
      omegaR (a • v+b • w) ((-b) • v+a • w) = (a^2+b^2)*omegaR v w ∧
      Real.sign (omegaR (a • v+b • w) ((-b) • v+a • w)) = Real.sign (omegaR v w)) ∧
    (∀ v2 w2 : Coord 1 → ℝ,
      (fun i => (v2 i : ℂ)-Complex.I*(w2 i : ℂ)) ≠ 0 →
      (complexify A).mulVec (fun i => (v2 i : ℂ)-Complex.I*(w2 i : ℂ)) =
        z • (fun i => (v2 i : ℂ)-Complex.I*(w2 i : ℂ)) →
      Real.sign (omegaR v2 w2) = Real.sign (omegaR v w)) ∧
    (complexify A).mulVec (fun i => (v i : ℂ)+Complex.I*(w i : ℂ)) =
      (star z) • (fun i => (v i : ℂ)+Complex.I*(w i : ℂ)) ∧
    omegaR v (-w) = -omegaR v w ∧
    omegaC (fun i => (v i : ℂ)-Complex.I*(w i : ℂ))
      (fun i => (v i : ℂ)+Complex.I*(w i : ℂ)) = 2*Complex.I*(omegaR v w : ℂ) :=
  X4CZE.main A hA z hz hzr v w he hev
