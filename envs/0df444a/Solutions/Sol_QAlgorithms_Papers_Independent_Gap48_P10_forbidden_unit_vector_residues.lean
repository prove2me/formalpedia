-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P10.forbidden_unit_vector_residues
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:58:17.057438+00:00
-- url     : https://prove2.me/submissions/2908c6f0-f2fb-4cf5-9154-6f2b7084999f

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

def g73p_w : ℂ := QAlgorithms.gateT true true

def g73p_m (a b c d : ℂ) : Matrix Bool Bool ℂ :=
  Matrix.of fun i j => if i then (if j then d else c) else (if j then b else a)

theorem g73p_m_mul (a b c d e f g h : ℂ) :
    g73p_m a b c d * g73p_m e f g h =
      g73p_m (a * e + b * g) (a * f + b * h) (c * e + d * g) (c * f + d * h) := by
  ext i j; cases i <;> cases j <;> simp [g73p_m, Matrix.mul_apply] <;> ring

theorem g73p_m_ext {a b c d a' b' c' d' : ℂ} (h1 : a = a') (h2 : b = b') (h3 : c = c')
    (h4 : d = d') : g73p_m a b c d = g73p_m a' b' c' d' := by subst h1 h2 h3 h4; rfl

theorem g73p_m_star (a b c d : ℂ) :
    star (g73p_m a b c d) = g73p_m (star a) (star c) (star b) (star d) := by
  ext i j; cases i <;> cases j <;> simp [g73p_m, Matrix.star_apply]

theorem g73p_w_eq : g73p_w =
    ((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I := by
  have : g73p_w = Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
    simp [g73p_w, QAlgorithms.gateT]; ring_nf
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]

theorem g73p_s2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; simp

theorem g73p_w2 : g73p_w ^ 2 = Complex.I := by
  rw [g73p_w_eq]; push_cast
  linear_combination ((1 + 2 * Complex.I + Complex.I ^ 2) / 4) * g73p_s2 + (1/2) * Complex.I_sq

theorem g73p_w4 : g73p_w ^ 4 = -1 := by
  rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, g73p_w2, Complex.I_sq]

theorem g73p_I : Complex.I = g73p_w ^ 2 := g73p_w2.symm

theorem g73p_sqrt2 : ((Real.sqrt 2 : ℝ) : ℂ) =
    g73p_w - g73p_w ^ 3 := by
  have h3 : g73p_w ^ 3 = g73p_w * Complex.I := by
    rw [← g73p_w2]; ring
  rw [h3, g73p_w_eq]; push_cast
  linear_combination ((Real.sqrt 2 : ℂ) / 2) * Complex.I_sq

theorem g73p_r : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) =
    (g73p_w - g73p_w ^ 3) / 2 := by
  rw [← g73p_sqrt2]
  have h : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have := g73p_s2; intro h0; rw [h0] at this; norm_num at this
  push_cast; field_simp; linear_combination (-1) * g73p_s2


theorem g73p_irr (x y : ℤ) (h : (x : ℝ) + (y : ℝ) * Real.sqrt 2 = 0) : x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · subst hy
    simp at h
    exact ⟨by exact_mod_cast h, rfl⟩
  · exfalso
    have hy' : (y : ℝ) ≠ 0 := by exact_mod_cast hy
    have : Real.sqrt 2 = ((-x / y : ℚ) : ℝ) := by
      push_cast; field_simp; linarith
    exact irrational_sqrt_two ⟨_, this.symm⟩

theorem g73p_col (U : RealMat) (hU : SpecialOrthogonal U)
    (k : ℕ) (A B : Matrix (Fin 3) (Fin 3) ℤ)
    (hcoeff : ∀ i j, U i j = ((A i j : ℝ) + (B i j : ℝ) * Real.sqrt 2) / (Real.sqrt 2) ^ k) :
    (∀ j l,
      (∑ i, (A i j * B i l + B i j * A i l)) = 0 ∧
      (∑ i, (A i j * A i l + 2 * (B i j * B i l))) =
        (2 : ℤ) ^ k * (if j = l then 1 else 0)) := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsk : Real.sqrt 2 ^ k * Real.sqrt 2 ^ k = (2 : ℝ) ^ k := by
    rw [← mul_pow, ← sq, hs2]
  have hpos : (2 : ℝ) ^ k ≠ 0 := by positivity
  intro j l
  have key : (∑ i, U i j * U i l) = if j = l then 1 else 0 := by
    have := congrFun (congrFun hU.1 j) l
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have e : ∀ i, U i j * U i l = (((A i j * A i l + 2 * (B i j * B i l) : ℤ) : ℝ) +
      ((A i j * B i l + B i j * A i l : ℤ) : ℝ) * Real.sqrt 2) / 2 ^ k := by
    intro i
    rw [hcoeff, hcoeff, div_mul_div_comm, hsk]
    congr 1
    push_cast
    linear_combination ((B i j : ℝ) * B i l) * hs2
  have hsum : (∑ i, U i j * U i l) =
      ((((∑ i, (A i j * A i l + 2 * (B i j * B i l))) : ℤ) : ℝ) +
        (((∑ i, (A i j * B i l + B i j * A i l)) : ℤ) : ℝ) * Real.sqrt 2) / 2 ^ k := by
    rw [Finset.sum_congr rfl (fun i _ => e i), ← Finset.sum_div]
    congr 1
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  rw [key] at hsum
  have h3 : ((((∑ i, (A i j * A i l + 2 * (B i j * B i l))) - 2 ^ k * (if j = l then 1 else 0) : ℤ) : ℝ) +
        (((∑ i, (A i j * B i l + B i j * A i l)) : ℤ) : ℝ) * Real.sqrt 2) = 0 := by
    have := hsum
    field_simp at this
    push_cast at this ⊢
    split_ifs at this ⊢ <;> linarith
  obtain ⟨h4, h5⟩ := g73p_irr _ _ h3
  exact ⟨h5, by linarith⟩

theorem g73p_colfull (U : RealMat) (hU : SpecialOrthogonal U)
    (k : ℕ) (A B : Matrix (Fin 3) (Fin 3) ℤ)
    (hcoeff : ∀ i j, U i j = ((A i j : ℝ) + (B i j : ℝ) * Real.sqrt 2) / (Real.sqrt 2) ^ k) :
    (∀ j l,
      (∑ i, (A i j * B i l + B i j * A i l)) = 0 ∧
      (∑ i, (A i j * A i l + 2 * (B i j * B i l))) =
        (2 : ℤ) ^ k * (if j = l then 1 else 0)) ∧
    (∀ j, (∑ i, A i j * B i j) = 0 ∧
      (∑ i, (A i j ^ 2 + 2 * B i j ^ 2)) = (2 : ℤ) ^ k) := by
  have H := g73p_col U hU k A B hcoeff
  refine ⟨H, fun j => ?_⟩
  obtain ⟨h1, h2⟩ := H j j
  constructor
  · have : (∑ i, (A i j * B i j + B i j * A i j)) = 2 * ∑ i, A i j * B i j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
    omega
  · simp only [if_true, mul_one] at h2
    rw [← h2]; exact Finset.sum_congr rfl (fun i _ => by ring)


theorem g73p_val_eq (a : Fin 4 → ℤ) : omegaCoordinatesValue a =
    (((a 3 : ℝ) + ((a 2 : ℝ) - a 0) * (Real.sqrt 2 / 2) : ℝ) : ℂ) +
    (((a 1 : ℝ) + ((a 2 : ℝ) + a 0) * (Real.sqrt 2 / 2) : ℝ) : ℂ) * Complex.I := by
  have hw : QAlgorithms.gateT true true = g73p_w := rfl
  simp only [omegaCoordinatesValue, hw]
  have h2 : g73p_w ^ 2 = Complex.I := g73p_w2
  have h3 : g73p_w ^ 3 = g73p_w * Complex.I := by rw [← g73p_w2]; ring
  rw [h3, h2, g73p_w_eq]
  push_cast
  linear_combination ((a 0 : ℂ) * ((Real.sqrt 2 : ℂ) / 2)) * Complex.I_sq

theorem g73p_normSq (a : Fin 4 → ℤ) : Complex.normSq (omegaCoordinatesValue a) =
    ((a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 : ℤ) : ℝ) +
    ((a 3 * (a 2 - a 0) + a 1 * (a 2 + a 0) : ℤ) : ℝ) * Real.sqrt 2 := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [g73p_val_eq, Complex.normSq_add_mul_I]
  push_cast
  linear_combination ((((a 2 : ℝ) - a 0) ^ 2 + ((a 2 : ℝ) + a 0) ^ 2) / 4) * hs2

theorem g73p_sq4 (x : ℤ) : x ^ 2 % 4 = x % 2 := by
  rcases Int.emod_two_eq_zero_or_one x with h | h
  · obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero h
    rw [h, hm, show (2 * m) ^ 2 = 4 * m ^ 2 by ring]; simp
  · have hm : x = 2 * (x / 2) + 1 := by omega
    rw [h, hm, show (2 * (x / 2) + 1) ^ 2 = 1 + 4 * ((x / 2) ^ 2 + x / 2) by ring,
      Int.add_mul_emod_self_left]; rfl

theorem g73p_par (x : ℤ) : ((x : ZMod 2) = 0 → x % 2 = 0) ∧ ((x : ZMod 2) = 1 → x % 2 = 1) := by
  constructor
  · intro h
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).1 h
    omega
  · intro h
    have h' : ((x : ℤ) : ZMod 2) = ((1 : ℤ) : ZMod 2) := by simpa using h
    have := (ZMod.intCast_eq_intCast_iff' x 1 2).1 h'
    simpa using this

theorem g73p_res4 (u : ℂ) (hu : InZomega u)
    (hru : residue u = bits 1 ∨ residue u = bits 2 ∨ residue u = bits 4 ∨ residue u = bits 8) :
    ∃ a : Fin 4 → ℤ, omegaCoordinatesValue a = u ∧ (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2) % 4 = 1 := by
  have hc : omegaCoordinatesValue (omegaCoordinates u) = u := by
    simp only [omegaCoordinates, dif_pos hu]; exact Classical.choose_spec hu
  refine ⟨omegaCoordinates u, hc, ?_⟩
  set a := omegaCoordinates u
  have e : ∀ n, residue u = bits n → ∀ i, (a i : ZMod 2) = bits n i := by
    intro n h i; rw [← h]; rfl
  have q0 := g73p_sq4 (a 0); have q1 := g73p_sq4 (a 1)
  have q2 := g73p_sq4 (a 2); have q3 := g73p_sq4 (a 3)
  have p0 := g73p_par (a 0); have p1 := g73p_par (a 1)
  have p2 := g73p_par (a 2); have p3 := g73p_par (a 3)
  generalize a 0 ^ 2 = s0 at *
  generalize a 1 ^ 2 = s1 at *
  generalize a 2 ^ 2 = s2 at *
  generalize a 3 ^ 2 = s3 at *
  rcases hru with h | h | h | h <;> have b := e _ h <;>
    have b0 := b 0 <;> have b1 := b 1 <;> have b2 := b 2 <;> have b3 := b 3 <;>
    simp [bits] at b0 b1 b2 b3 <;>
    have c0 := p0.1 <;> have d0 := p0.2 <;> have c1 := p1.1 <;> have d1 := p1.2 <;>
    have c2 := p2.1 <;> have d2 := p2.2 <;> have c3 := p3.1 <;> have d3 := p3.2 <;>
    simp_all <;> omega

theorem g73p_forb (k : ℕ) (hk : 2 ≤ k)
    (u t : ℂ) (hu : InZomega u) (ht : InZomega t)
    (hru : residue u = bits 1 ∨ residue u = bits 2 ∨ residue u = bits 4 ∨ residue u = bits 8)
    (hrt : residue t = bits 1 ∨ residue t = bits 2 ∨ residue t = bits 4 ∨ residue t = bits 8) :
    Complex.normSq (u / ((Real.sqrt 2 : ℝ) : ℂ) ^ k) +
      Complex.normSq (t / ((Real.sqrt 2 : ℝ) : ℂ) ^ k) ≠ 1 := by
  obtain ⟨a, rfl, ha⟩ := g73p_res4 u hu hru
  obtain ⟨b, rfl, hb⟩ := g73p_res4 t ht hrt
  intro h
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Complex.normSq (((Real.sqrt 2 : ℝ) : ℂ) ^ k) = 2 ^ k := by
    rw [map_pow, Complex.normSq_ofReal, ← sq, hs2]
  rw [Complex.normSq_div, Complex.normSq_div, hn, g73p_normSq, g73p_normSq] at h
  have hpos : (2 : ℝ) ^ k ≠ 0 := by positivity
  field_simp at h
  have h3 : (((a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2) + (b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 + b 3 ^ 2) - 2 ^ k : ℤ) : ℝ) +
      (((a 3 * (a 2 - a 0) + a 1 * (a 2 + a 0)) + (b 3 * (b 2 - b 0) + b 1 * (b 2 + b 0)) : ℤ) : ℝ) *
        Real.sqrt 2 = 0 := by
    push_cast at h ⊢; linarith
  have h4 := (g73p_irr _ _ h3).1
  have h5 : (2 : ℤ) ^ k % 4 = 0 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add]; norm_num
  omega


/-- Lemma 7.7, PDF p.9. The vector is divided by sqrt(2)^k; k>=2 is essential.
Non-unit norm is expressed as the sum of its two actual squared amplitudes. -/
theorem solution (k : ℕ) (hk : 2 ≤ k)
    (u t : ℂ) (hu : InZomega u) (ht : InZomega t)
    (hru : residue u = bits 1 ∨ residue u = bits 2 ∨ residue u = bits 4 ∨ residue u = bits 8)
    (hrt : residue t = bits 1 ∨ residue t = bits 2 ∨ residue t = bits 4 ∨ residue t = bits 8) :
    Complex.normSq (u / ((Real.sqrt 2 : ℝ) : ℂ) ^ k) +
      Complex.normSq (t / ((Real.sqrt 2 : ℝ) : ℂ) ^ k) ≠ 1 := by
  exact g73p_forb k hk u t hu ht hru hrt


end
