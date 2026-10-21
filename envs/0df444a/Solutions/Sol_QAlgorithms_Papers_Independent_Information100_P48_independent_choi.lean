-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P48.independent_choi
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T08:46:40.612085+00:00
-- url     : https://prove2.me/submissions/dda2eb2a-19b7-4a01-b69a-7b6d1051a9db

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P48

namespace G55IND

lemma cos_pa (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : Real.cos (principalAngle g) = Real.sqrt (1 - g) := by
  unfold principalAngle
  rw [Real.cos_arcsin, Real.sq_sqrt hg0]

lemma sin_pa (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : Real.sin (principalAngle g) = Real.sqrt g := by
  unfold principalAngle
  rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg g]) (Real.sqrt_le_one.mpr hg1)]

set_option maxHeartbeats 4000000 in
lemma choi_ind (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    choi (independentADC g false) = pairMatrix !![(1 / 2 : ℂ), 0, 0, (Real.sqrt (1 - g) : ℂ) / 2;
      0, 0, 0, 0; 0, 0, (g : ℂ) / 4, 0;
      (Real.sqrt (1 - g) : ℂ) / 2, 0, 0, ((1 - g : ℝ) : ℂ) / 2] := by
  have h1 : (Real.sqrt (1 - g) : ℂ) ^ 2 = 1 - (g : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring
  have h2 : (Real.sqrt g : ℂ) ^ 2 = (g : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hg0]
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [choi, QAlgorithms.idTensorSuperop, independentADC, branch, cross, selectedOperator, outcomeSign,
      traceEnv, cleanInput, embed0, embed1, dilation, adcUnitary, cos_pa g hg0 hg1, sin_pa g hg0 hg1, bellDensity,
      Matrix.mul_apply, pairMatrix, pairIndex, Fintype.sum_prod_type, Matrix.kronecker, Matrix.single_apply] <;>
    ring_nf <;> (try simp [h1, h2]) <;> (try ring_nf)

lemma cs3 (a0 a1 a2 p0 p1 p2 : ℝ) :
    (a0 * p0 + a1 * p1 + a2 * p2) ^ 2 ≤ (a0 ^ 2 + a1 ^ 2 + a2 ^ 2) * (p0 ^ 2 + p1 ^ 2 + p2 ^ 2) := by
  nlinarith [sq_nonneg (a0 * p1 - a1 * p0), sq_nonneg (a0 * p2 - a2 * p0), sq_nonneg (a1 * p2 - a2 * p1)]

lemma half (c : ℝ) (a : Fin 3 → ℝ) (ha : ∑ i, a i ^ 2 = 1) (u0 u1 u2 : ℝ) :
    c * (a 0 * u0 - a 1 * u1) + a 2 * u2 ≤ Real.sqrt (c ^ 2 * (u0 ^ 2 + u1 ^ 2) + u2 ^ 2) := by
  rw [Fin.sum_univ_three] at ha
  have hc := cs3 (a 0) (a 1) (a 2) (c * u0) (-(c * u1)) u2
  rw [ha, one_mul] at hc
  rw [show (c * u0) ^ 2 + (-(c * u1)) ^ 2 + u2 ^ 2 = c ^ 2 * (u0 ^ 2 + u1 ^ 2) + u2 ^ 2 by ring] at hc
  have := Real.abs_le_sqrt hc
  have e : c * (a 0 * u0 - a 1 * u1) + a 2 * u2 = a 0 * (c * u0) + a 1 * (-(c * u1)) + a 2 * u2 := by ring
  rw [e]; exact (le_abs_self _).trans this

lemma sq_bound (c x y X Y A B a b : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hX : X = c ^ 2 * A + a ^ 2) (hY : Y = c ^ 2 * B + b ^ 2) (hPQ : A + a ^ 2 + (B + b ^ 2) = 4)
    (hbes : a ^ 2 * b ^ 2 ≤ A * B) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hx : x ^ 2 = X) (hy : y ^ 2 = Y) :
    (x + y) ^ 2 ≤ 4 * (1 + c ^ 2) := by
  have hc2 : c ^ 2 ≤ 1 := by nlinarith
  obtain ⟨P, hP⟩ : ∃ P, P = A + a ^ 2 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = B + b ^ 2 := ⟨_, rfl⟩
  have hPQ' : P + Q = 4 := by rw [hP, hQ]; exact hPQ
  have hkey : X * Q + Y * P ≤ (1 + c ^ 2) * (P * Q) := by
    have e : (1 + c ^ 2) * (P * Q) - (X * Q + Y * P) = (1 - c ^ 2) * (A * B - a ^ 2 * b ^ 2) := by
      rw [hX, hY, hP, hQ]; ring
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2) (sub_nonneg.mpr hbes)]
  have hXP : X ≤ P := by rw [hX, hP]; nlinarith
  have hYQ : Y ≤ Q := by rw [hY, hQ]; nlinarith
  have hX0 : 0 ≤ X := by rw [← hx]; positivity
  have hY0 : 0 ≤ Y := by rw [← hy]; positivity
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  rcases hP0.eq_or_lt with hP' | hP'
  · have : X = 0 := le_antisymm (hP' ▸ hXP) hX0
    have hx' : x = 0 := by nlinarith
    rw [hx', zero_add, hy]; nlinarith
  rcases hQ0.eq_or_lt with hQ' | hQ'
  · have : Y = 0 := le_antisymm (hQ' ▸ hYQ) hY0
    have hy' : y = 0 := by nlinarith
    rw [hy', add_zero, hx]; nlinarith
  have hcs : (x + y) ^ 2 * (P * Q) ≤ (P + Q) * (x ^ 2 * Q + y ^ 2 * P) := by
    nlinarith [sq_nonneg (x * Q - y * P)]
  rw [hx, hy, hPQ'] at hcs
  have hPQpos : 0 < P * Q := mul_pos hP' hQ'
  have : (x + y) ^ 2 * (P * Q) ≤ 4 * (1 + c ^ 2) * (P * Q) := by nlinarith
  exact le_of_mul_le_mul_right this hPQpos

lemma horo (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (a0 a1 b0 b1 : Fin 3 → ℝ)
    (ha0 : ∑ i, a0 i ^ 2 = 1) (ha1 : ∑ i, a1 i ^ 2 = 1) (hb0 : ∑ i, b0 i ^ 2 = 1) (hb1 : ∑ i, b1 i ^ 2 = 1) :
    c * (a0 0 * (b0 0 + b1 0) - a0 1 * (b0 1 + b1 1) + a1 0 * (b0 0 - b1 0) - a1 1 * (b0 1 - b1 1)) +
      (a0 2 * (b0 2 + b1 2) + a1 2 * (b0 2 - b1 2)) ≤ 2 * Real.sqrt (1 + c ^ 2) := by
  have e1 := half c a0 ha0 (b0 0 + b1 0) (b0 1 + b1 1) (b0 2 + b1 2)
  have e2 := half c a1 ha1 (b0 0 - b1 0) (b0 1 - b1 1) (b0 2 - b1 2)
  rw [Fin.sum_univ_three] at hb0 hb1
  have hbes : (b0 2 + b1 2) ^ 2 * (b0 2 - b1 2) ^ 2 ≤
      ((b0 0 + b1 0) ^ 2 + (b0 1 + b1 1) ^ 2) * ((b0 0 - b1 0) ^ 2 + (b0 1 - b1 1) ^ 2) := by
    have h' : (b0 0 + b1 0) * (b0 0 - b1 0) + (b0 1 + b1 1) * (b0 1 - b1 1) =
        -((b0 2 + b1 2) * (b0 2 - b1 2)) := by nlinarith
    have hcs2 : ((b0 0 + b1 0) * (b0 0 - b1 0) + (b0 1 + b1 1) * (b0 1 - b1 1)) ^ 2 ≤
        ((b0 0 + b1 0) ^ 2 + (b0 1 + b1 1) ^ 2) * ((b0 0 - b1 0) ^ 2 + (b0 1 - b1 1) ^ 2) := by
      nlinarith [sq_nonneg ((b0 0 + b1 0) * (b0 1 - b1 1) - (b0 1 + b1 1) * (b0 0 - b1 0))]
    rw [h'] at hcs2; nlinarith
  have hsq := sq_bound c _ _ _ _ _ _ _ _ hc0 hc1 (by positivity) (by positivity) rfl rfl
    (by nlinarith) hbes (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sq_sqrt (by positivity))
    (Real.sq_sqrt (by positivity))
  have h4 : Real.sqrt (4 * (1 + c ^ 2)) = 2 * Real.sqrt (1 + c ^ 2) := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hfin := (le_abs_self _).trans (Real.abs_le_sqrt hsq)
  rw [h4] at hfin
  linarith


lemma half_bound (s t : ℝ) (hs : 0 ≤ s) (ht : |t| ≤ s) (a : Fin 3 → ℝ) (ha : ∑ i, a i ^ 2 = 1)
    (u0 u1 u2 : ℝ) :
    s * (a 0 * u0 - a 1 * u1) + t * (a 2 * u2) ≤ s * Real.sqrt (u0 ^ 2 + u1 ^ 2 + u2 ^ 2) := by
  rw [Fin.sum_univ_three] at ha
  have hc := cs3 (a 0) (a 1) (a 2) (s * u0) (-(s * u1)) (t * u2)
  rw [ha, one_mul] at hc
  have ht2 : t ^ 2 ≤ s ^ 2 := by
    have := sq_abs t; nlinarith [abs_nonneg t]
  have hle : (s * u0) ^ 2 + (-(s * u1)) ^ 2 + (t * u2) ^ 2 ≤ (s * Real.sqrt (u0 ^ 2 + u1 ^ 2 + u2 ^ 2)) ^ 2 := by
    have hq := Real.sq_sqrt (show 0 ≤ u0 ^ 2 + u1 ^ 2 + u2 ^ 2 by positivity)
    rw [show (s * Real.sqrt (u0 ^ 2 + u1 ^ 2 + u2 ^ 2)) ^ 2 = s ^ 2 * (Real.sqrt (u0 ^ 2 + u1 ^ 2 + u2 ^ 2)) ^ 2 by ring,
      hq]
    nlinarith [sq_nonneg u2, mul_le_mul_of_nonneg_right ht2 (sq_nonneg u2)]
  have := Real.abs_le_sqrt (hc.trans hle)
  rw [Real.sqrt_sq (by positivity)] at this
  have e : s * (a 0 * u0 - a 1 * u1) + t * (a 2 * u2) = a 0 * (s * u0) + a 1 * (-(s * u1)) + a 2 * (t * u2) := by ring
  rw [e]; exact (le_abs_self _).trans this


lemma tr_ind (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : (choi (independentADC g false)).trace.re = 1 - g / 4 := by
  rw [choi_ind g hg0 hg1]
  simp [Matrix.trace, pairMatrix, pairIndex, Fintype.sum_prod_type]
  ring

lemma cond_ind (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    conditionalChoi (independentADC g false) = independentChoiMatrix g := by
  unfold conditionalChoi QAlgorithms.Papers.Independent.Information100.P48.normalize
  rw [tr_ind g hg0 hg1, choi_ind g hg0 hg1]
  have h4g : (4 - (g : ℂ)) ≠ 0 := by
    intro h; have : (4 - g : ℝ) = 0 := by exact_mod_cast h
    linarith
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [independentChoiMatrix, pairMatrix, pairIndex] <;> field_simp <;> ring

lemma dens_ind (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : IsDensityMatrix (independentChoiMatrix g) := by
  have h4g : (0 : ℝ) < 4 - g := by linarith
  have h1 : (Real.sqrt (1 - g) : ℂ) * (Real.sqrt (1 - g) : ℂ) = ((1 - g : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  set v : Bool × Bool → ℂ := fun p => if p = (false, false) then 1
    else if p = (true, true) then (Real.sqrt (1 - g) : ℂ) else 0 with hv
  have e : independentChoiMatrix g = (((4 - g)⁻¹ : ℝ) : ℂ) • ((2 : ℂ) • Matrix.vecMulVec v (star v) +
      Matrix.diagonal (fun p : Bool × Bool => if p = (true, false) then (g : ℂ) else 0)) := by
    ext ⟨a, b⟩ ⟨c, d⟩
    cases a <;> cases b <;> cases c <;> cases d <;>
      simp [independentChoiMatrix, pairMatrix, pairIndex, hv, Matrix.vecMulVec_apply, h1, Matrix.diagonal_apply] <;>
      ring
  refine ⟨?_, ?_⟩
  · rw [e]
    refine Matrix.PosSemidef.smul ?_ (by exact_mod_cast (inv_pos.mpr h4g).le)
    refine ((Matrix.posSemidef_vecMulVec_self_star v).smul (by norm_num)).add
      (Matrix.PosSemidef.diagonal fun p => ?_)
    simp only [Pi.zero_apply]; split_ifs
    · exact_mod_cast hg0
    · exact le_refl _
  · simp [Matrix.trace, independentChoiMatrix, pairMatrix, pairIndex, Fintype.sum_prod_type]
    have : ((4 : ℂ) - g) ≠ 0 := by
      intro h; have : (4 - g : ℝ) = 0 := by exact_mod_cast h
      linarith
    field_simp
    ring

lemma hn4 (g : ℝ) : Complex.normSq (4 - (g : ℂ)) = (4 - g) ^ 2 := by
  rw [show (4 : ℂ) - g = ((4 - g : ℝ) : ℂ) by push_cast; ring, Complex.normSq_ofReal]; ring

lemma ctensor_ind (g : ℝ) (hg1 : g ≤ 1) : correlationTensor (independentChoiMatrix g) =
    Matrix.diagonal ![4 * Real.sqrt (1 - g) / (4 - g), -4 * Real.sqrt (1 - g) / (4 - g), (4 - 3 * g) / (4 - g)] := by
  have h4g : (4 - g : ℝ) ≠ 0 := by intro h; linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [correlationTensor, pauli, pauliX, pauliY, pauliZ, independentChoiMatrix, pairMatrix, pairIndex,
      Matrix.mul_apply, Matrix.trace, Fintype.sum_prod_type, Matrix.kronecker, Matrix.diagonal_apply, hn4] <;>
    field_simp <;> ring_nf

lemma chsh_ind (g : ℝ) (hg1 : g ≤ 1) (a0 a1 b0 b1 : Fin 3 → ℝ) :
    spatialCHSH (independentChoiMatrix g) a0 a1 b0 b1 =
      (4 * Real.sqrt (1 - g) / (4 - g)) * (a0 0 * (b0 0 + b1 0) - a0 1 * (b0 1 + b1 1) + a1 0 * (b0 0 - b1 0)
        - a1 1 * (b0 1 - b1 1)) + ((4 - 3 * g) / (4 - g)) * (a0 2 * (b0 2 + b1 2) + a1 2 * (b0 2 - b1 2)) := by
  have h4g : (4 - g : ℝ) ≠ 0 := by intro h; linarith
  simp only [spatialCHSH, bloch, Fin.sum_univ_three, pauli]
  simp [pauliX, pauliY, pauliZ, independentChoiMatrix, pairMatrix, pairIndex, Matrix.mul_apply, Matrix.trace,
    Fintype.sum_prod_type, Matrix.kronecker, Matrix.diagonal_apply, hn4]
  field_simp
  ring


lemma split2 (c t a0x a0y a0z a1x a1y a1z u0 u1 u2 w0 w1 w2 : ℝ) :
    c * (a0x * u0 - a0y * u1 + a1x * w0 - a1y * w1) + t * (a0z * u2 + a1z * w2) =
      (c * (a0x * u0 - a0y * u1) + t * (a0z * u2)) + (c * (a1x * w0 - a1y * w1) + t * (a1z * w2)) := by ring

set_option maxHeartbeats 3000000 in
lemma greatest_ind (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    IsGreatest (spatialValues (independentChoiMatrix g)) (independentSpatialMaximum g) := by
  set s := Real.sqrt (1 - g) with hsdef
  have h4g : (0 : ℝ) < 4 - g := by linarith
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - g by linarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set c := 4 * s / (4 - g) with hc
  set t := (4 - 3 * g) / (4 - g) with ht
  have hc0 : 0 ≤ c := by positivity
  have ht0 : 0 < t := by apply div_pos <;> linarith
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2pos : 0 < Real.sqrt 2 := by positivity
  unfold independentSpatialMaximum
  split_ifs with hg89
  · -- equatorial maximum
    have htc : |t| ≤ c := by
      rw [abs_of_pos ht0, ht, hc]
      apply div_le_div_of_nonneg_right _ h4g.le
      have : (4 - 3 * g) ^ 2 ≤ (4 * s) ^ 2 := by rw [mul_pow, hs2]; nlinarith
      nlinarith [sq_nonneg (4 - 3 * g), sq_nonneg (4 * s)]
    have htarget : 8 * Real.sqrt (2 - 2 * g) / (4 - g) = 2 * Real.sqrt 2 * c := by
      rw [show (2 : ℝ) - 2 * g = 2 * (1 - g) by ring, Real.sqrt_mul (by norm_num), hc]; ring
    rw [htarget]
    constructor
    · refine ⟨![1, 0, 0], ![0, -1, 0], ![(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹, 0],
        ![(Real.sqrt 2)⁻¹, -(Real.sqrt 2)⁻¹, 0], ?_, ?_, ?_, ?_, ?_⟩
      · simp [UnitDirection, Fin.sum_univ_three]
      · simp [UnitDirection, Fin.sum_univ_three]
      · simp [UnitDirection, Fin.sum_univ_three]; field_simp; nlinarith
      · simp [UnitDirection, Fin.sum_univ_three]; field_simp; nlinarith
      · rw [chsh_ind g hg1, ← hc, ← ht]
        simp
        field_simp
        nlinarith
    · rintro v ⟨a0, a1, b0, b1, ha0, ha1, hb0, hb1, rfl⟩
      rw [chsh_ind g hg1, ← hc, ← ht, split2]
      have e1 := half_bound c t hc0 htc a0 ha0 (b0 0 + b1 0) (b0 1 + b1 1) (b0 2 + b1 2)
      have e2 := half_bound c t hc0 htc a1 ha1 (b0 0 - b1 0) (b0 1 - b1 1) (b0 2 - b1 2)
      unfold UnitDirection at hb0 hb1
      rw [Fin.sum_univ_three] at hb0 hb1
      set U := (b0 0 + b1 0) ^ 2 + (b0 1 + b1 1) ^ 2 + (b0 2 + b1 2) ^ 2
      set W := (b0 0 - b1 0) ^ 2 + (b0 1 - b1 1) ^ 2 + (b0 2 - b1 2) ^ 2
      have hUW : U + W = 4 := by simp only [U, W]; nlinarith
      have hU0 : 0 ≤ U := by positivity
      have hW0 : 0 ≤ W := by positivity
      have hsum : Real.sqrt U + Real.sqrt W ≤ 2 * Real.sqrt 2 := by
        have hu := Real.sq_sqrt hU0
        have hw := Real.sq_sqrt hW0
        have h22 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        nlinarith [sq_nonneg (Real.sqrt U - Real.sqrt W), Real.sqrt_nonneg U, Real.sqrt_nonneg W]
      have : c * Real.sqrt U + c * Real.sqrt W ≤ 2 * Real.sqrt 2 * c := by nlinarith
      linarith
  · -- polar maximum
    push Not at hg89
    set c' := c / t with hc'
    have hc'0 : 0 ≤ c' := by positivity
    have hc'1 : c' ≤ 1 := by
      rw [hc', div_le_one ht0, ht, hc]
      apply div_le_div_of_nonneg_right _ h4g.le
      have hsq : (4 * s) ^ 2 ≤ (4 - 3 * g) ^ 2 := by rw [mul_pow, hs2]; nlinarith
      nlinarith [sq_nonneg (4 - 3 * g), sq_nonneg (4 * s), mul_nonneg hs0 (show (0:ℝ) ≤ 4 by norm_num)]
    have hcc : c = t * c' := by rw [hc']; field_simp
    set r := Real.sqrt (1 + c' ^ 2) with hr
    have hr2 : r ^ 2 = 1 + c' ^ 2 := Real.sq_sqrt (by positivity)
    have hr0 : 0 < r := Real.sqrt_pos.mpr (by positivity)
    have htarget : 2 * Real.sqrt (16 * (1 - g) + (4 - 3 * g) ^ 2) / (4 - g) = 2 * t * r := by
      have e : 16 * (1 - g) + (4 - 3 * g) ^ 2 = ((4 - g) * t * r) ^ 2 := by
        rw [mul_pow, mul_pow, hr2, ht]
        have : c' ^ 2 = (4 * s) ^ 2 / (4 - 3 * g) ^ 2 := by
          rw [hc', hc, ht, div_div_div_cancel_right₀ h4g.ne', div_pow]
        rw [this, mul_pow, hs2]
        have h43 : (4 - 3 * g) ≠ 0 := by intro h; linarith
        have h4 : (4 - g) ≠ 0 := h4g.ne'
        clear_value c t c' r s
        generalize hk : 4 - 3 * g = k at *
        generalize hm : 4 - g = m at *
        have hk2 : k ^ 2 ≠ 0 := pow_ne_zero 2 h43
        have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 h4
        rw [div_pow, mul_div_assoc', mul_div_cancel_left₀ _ hm2, mul_add, mul_one, mul_div_assoc',
          mul_div_cancel_left₀ _ hk2]
        ring
      rw [e, Real.sqrt_sq (by positivity)]
      field_simp
    rw [htarget]
    constructor
    · refine ⟨![0, 0, 1], ![1, 0, 0], ![c' / r, 0, 1 / r], ![-(c' / r), 0, 1 / r], ?_, ?_, ?_, ?_, ?_⟩
      · simp [UnitDirection, Fin.sum_univ_three]
      · simp [UnitDirection, Fin.sum_univ_three]
      · simp only [UnitDirection, Fin.sum_univ_three]; simp; field_simp; linarith
      · simp only [UnitDirection, Fin.sum_univ_three]; simp; field_simp; linarith
      · rw [chsh_ind g hg1, ← hc, ← ht, hcc]
        simp
        field_simp
        nlinarith
    · rintro v ⟨a0, a1, b0, b1, ha0, ha1, hb0, hb1, rfl⟩
      rw [chsh_ind g hg1, ← hc, ← ht, hcc]
      have := horo c' hc'0 hc'1 a0 a1 b0 b1 ha0 ha1 hb0 hb1
      have e : t * c' * (a0 0 * (b0 0 + b1 0) - a0 1 * (b0 1 + b1 1) + a1 0 * (b0 0 - b1 0) - a1 1 * (b0 1 - b1 1))
          + t * (a0 2 * (b0 2 + b1 2) + a1 2 * (b0 2 - b1 2)) =
          t * (c' * (a0 0 * (b0 0 + b1 0) - a0 1 * (b0 1 + b1 1) + a1 0 * (b0 0 - b1 0) - a1 1 * (b0 1 - b1 1)) +
            (a0 2 * (b0 2 + b1 2) + a1 2 * (b0 2 - b1 2))) := by ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left this ht0.le]


lemma thr_ind (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    (2 < independentSpatialMaximum g ↔ g < independentCritical) := by
  have h4g : (0 : ℝ) < 4 - g := by linarith
  have h10 := Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)
  have h10a : (3.16 : ℝ) < Real.sqrt 10 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h10b : Real.sqrt 10 < 3.17 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  unfold independentSpatialMaximum independentCritical
  split_ifs with hg89
  · have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 - 2 * g by linarith)
    have hs0 := Real.sqrt_nonneg (2 - 2 * g)
    rw [lt_div_iff₀ h4g]
    constructor
    · intro h
      have h1 : (4 - g) ^ 2 < (4 * Real.sqrt (2 - 2 * g)) ^ 2 := by nlinarith
      rw [mul_pow, hs] at h1
      nlinarith [Real.sqrt_nonneg 10]
    · intro h
      have h1 : (4 - g) ^ 2 < (4 * Real.sqrt (2 - 2 * g)) ^ 2 := by
        rw [mul_pow, hs]; nlinarith [Real.sqrt_nonneg 10]
      have := (pow_lt_pow_iff_left₀ h4g.le (by positivity) two_ne_zero).mp h1
      linarith
  · push Not at hg89
    constructor
    · intro h
      exfalso
      rw [lt_div_iff₀ h4g] at h
      have hX : 0 ≤ 16 * (1 - g) + (4 - 3 * g) ^ 2 := by nlinarith
      have hs := Real.sq_sqrt hX
      have h1 : (4 - g) ^ 2 < (Real.sqrt (16 * (1 - g) + (4 - 3 * g) ^ 2)) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (16 * (1 - g) + (4 - 3 * g) ^ 2)]
      rw [hs] at h1
      nlinarith
    · intro h; exfalso; linarith

end G55IND

open G55IND in
theorem solution (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    (choi (independentADC g false)).trace.re = 1 - g / 4 ∧
    conditionalChoi (independentADC g false) = independentChoiMatrix g ∧
    IsDensityMatrix (conditionalChoi (independentADC g false)) ∧
    correlationTensor (conditionalChoi (independentADC g false)) =
      Matrix.diagonal ![4 * Real.sqrt (1 - g) / (4 - g),
        -4 * Real.sqrt (1 - g) / (4 - g), (4 - 3 * g) / (4 - g)] ∧
    IsGreatest (spatialValues (conditionalChoi (independentADC g false)))
      (independentSpatialMaximum g) ∧
    (2 < independentSpatialMaximum g ↔ g < independentCritical) := by
  have h := cond_ind g hg0 hg1
  refine ⟨tr_ind g hg0 hg1, h, by rw [h]; exact dens_ind g hg0 hg1, by rw [h]; exact ctensor_ind g hg1,
    by rw [h]; exact greatest_ind g hg0 hg1, thr_ind g hg0 hg1⟩
