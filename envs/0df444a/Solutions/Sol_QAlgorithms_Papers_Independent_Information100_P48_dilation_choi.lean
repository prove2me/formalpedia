-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P48.dilation_choi
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T08:23:31.788338+00:00
-- url     : https://prove2.me/submissions/b9216594-56ed-49c7-8890-f04651fc22a8

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P48

namespace G55DIL

lemma cos_pa (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : Real.cos (principalAngle g) = Real.sqrt (1 - g) := by
  unfold principalAngle
  rw [Real.cos_arcsin, Real.sq_sqrt hg0]

lemma sin_pa (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : Real.sin (principalAngle g) = Real.sqrt g := by
  unfold principalAngle
  rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg g]) (Real.sqrt_le_one.mpr hg1)]

lemma choi_sh (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    choi (sharedADC g false) = pairMatrix !![(1 / 2 : ℂ), 0, 0, (Real.sqrt (1 - g) : ℂ) / 2;
      0, 0, 0, 0; 0, 0, 0, 0; (Real.sqrt (1 - g) : ℂ) / 2, 0, 0, ((1 - g : ℝ) : ℂ) / 2] := by
  have h1 : (Real.sqrt (1 - g) : ℂ) ^ 2 = 1 - (g : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [choi, QAlgorithms.idTensorSuperop, sharedADC, branch, cross, selectedOperator, outcomeSign,
      traceEnv, cleanInput, dilation, adcUnitary, cos_pa g hg0 hg1, sin_pa g hg0 hg1, bellDensity,
      Matrix.mul_apply, pairMatrix, pairIndex, Fintype.sum_prod_type, Matrix.kronecker, Matrix.single_apply] <;>
    ring_nf <;> (try simp [h1]) <;> (try ring_nf)


lemma tr_sh (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : (choi (sharedADC g false)).trace.re = 1 - g / 2 := by
  rw [choi_sh g hg0 hg1]
  simp [Matrix.trace, pairMatrix, pairIndex, Fintype.sum_prod_type]
  ring

lemma cond_sh (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : conditionalChoi (sharedADC g false) = sharedChoiMatrix g := by
  unfold conditionalChoi QAlgorithms.Papers.Independent.Information100.P48.normalize
  rw [tr_sh g hg0 hg1, choi_sh g hg0 hg1]
  have h2g : (2 - (g : ℂ)) ≠ 0 := by
    intro h; have : (2 - g : ℝ) = 0 := by exact_mod_cast h
    linarith
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [sharedChoiMatrix, pairMatrix, pairIndex] <;> field_simp <;> ring

lemma dens_sh (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : IsDensityMatrix (sharedChoiMatrix g) := by
  have h2g : (0 : ℝ) < 2 - g := by linarith
  have h1 : (Real.sqrt (1 - g) : ℂ) * (Real.sqrt (1 - g) : ℂ) = ((1 - g : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  set v : Bool × Bool → ℂ := fun p => if p = (false, false) then 1
    else if p = (true, true) then (Real.sqrt (1 - g) : ℂ) else 0 with hv
  have e : sharedChoiMatrix g = (((2 - g)⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec v (star v) := by
    ext ⟨a, b⟩ ⟨c, d⟩
    cases a <;> cases b <;> cases c <;> cases d <;>
      simp [sharedChoiMatrix, pairMatrix, pairIndex, hv, Matrix.vecMulVec_apply, h1] <;> ring
  refine ⟨?_, ?_⟩
  · rw [e]; exact (Matrix.posSemidef_vecMulVec_self_star v).smul (by exact_mod_cast (inv_pos.mpr h2g).le)
  · simp [Matrix.trace, sharedChoiMatrix, pairMatrix, pairIndex, Fintype.sum_prod_type]
    have : ((2 : ℂ) - g) ≠ 0 := by
      intro h; have : (2 - g : ℝ) = 0 := by exact_mod_cast h
      linarith
    field_simp
    ring

lemma ctensor_sh (g : ℝ) (hg1 : g ≤ 1) : correlationTensor (sharedChoiMatrix g) =
    Matrix.diagonal ![2 * Real.sqrt (1 - g) / (2 - g), -2 * Real.sqrt (1 - g) / (2 - g), 1] := by
  have h2g : (2 - g : ℝ) ≠ 0 := by intro h; linarith
  have hn : Complex.normSq (2 - (g : ℂ)) = (2 - g) ^ 2 := by
    rw [show (2 : ℂ) - g = ((2 - g : ℝ) : ℂ) by push_cast; ring, Complex.normSq_ofReal]; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [correlationTensor, pauli, pauliX, pauliY, pauliZ, sharedChoiMatrix, pairMatrix, pairIndex,
      Matrix.mul_apply, Matrix.trace, Fintype.sum_prod_type, Matrix.kronecker, Matrix.diagonal_apply, hn] <;>
    field_simp <;> ring_nf


lemma chsh_sh (g : ℝ) (hg1 : g ≤ 1) (a0 a1 b0 b1 : Fin 3 → ℝ) :
    spatialCHSH (sharedChoiMatrix g) a0 a1 b0 b1 =
      (2 * Real.sqrt (1 - g) / (2 - g)) * (a0 0 * (b0 0 + b1 0) - a0 1 * (b0 1 + b1 1) + a1 0 * (b0 0 - b1 0)
        - a1 1 * (b0 1 - b1 1)) + (a0 2 * (b0 2 + b1 2) + a1 2 * (b0 2 - b1 2)) := by
  have h2g : (2 - g : ℝ) ≠ 0 := by intro h; linarith
  have hn : Complex.normSq (2 - (g : ℂ)) = (2 - g) ^ 2 := by
    rw [show (2 : ℂ) - g = ((2 - g : ℝ) : ℂ) by push_cast; ring, Complex.normSq_ofReal]; ring
  simp only [spatialCHSH, bloch, Fin.sum_univ_three, pauli]
  simp [pauliX, pauliY, pauliZ, sharedChoiMatrix, pairMatrix, pairIndex, Matrix.mul_apply, Matrix.trace,
    Fintype.sum_prod_type, Matrix.kronecker, Matrix.diagonal_apply, hn]
  field_simp
  ring

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


lemma greatest_sh (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    IsGreatest (spatialValues (sharedChoiMatrix g)) (2 * Real.sqrt (1 + 4 * (1 - g) / (2 - g) ^ 2)) := by
  set c := 2 * Real.sqrt (1 - g) / (2 - g) with hc
  have h2g : (0 : ℝ) < 2 - g := by linarith
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - g by linarith)
  have hs0 := Real.sqrt_nonneg (1 - g)
  have hc2 : c ^ 2 = 4 * (1 - g) / (2 - g) ^ 2 := by rw [hc, div_pow, mul_pow, hs]; ring
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one h2g]
    nlinarith [sq_nonneg (Real.sqrt (1 - g) - 1)]
  rw [← hc2]
  set r := Real.sqrt (1 + c ^ 2) with hr
  have hr2 : r ^ 2 = 1 + c ^ 2 := Real.sq_sqrt (by positivity)
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by positivity)
  constructor
  · refine ⟨![0, 0, 1], ![1, 0, 0], ![c / r, 0, 1 / r], ![-(c / r), 0, 1 / r], ?_, ?_, ?_, ?_, ?_⟩
    · simp [UnitDirection, Fin.sum_univ_three]
    · simp [UnitDirection, Fin.sum_univ_three]
    · simp only [UnitDirection, Fin.sum_univ_three]; simp; field_simp; linarith
    · simp only [UnitDirection, Fin.sum_univ_three]; simp; field_simp; linarith
    · rw [chsh_sh g hg1, ← hc]
      simp
      field_simp
      nlinarith
  · rintro v ⟨a0, a1, b0, b1, ha0, ha1, hb0, hb1, rfl⟩
    rw [chsh_sh g hg1, ← hc]
    exact horo c hc0 hc1 a0 a1 b0 b1 ha0 ha1 hb0 hb1

lemma thr_sh (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    (2 < 2 * Real.sqrt (1 + 4 * (1 - g) / (2 - g) ^ 2) ↔ g < 1) := by
  have h2g : (0 : ℝ) < 2 - g := by linarith
  constructor
  · intro h
    by_contra hg
    have : g = 1 := by linarith
    subst this
    norm_num at h
  · intro h
    have hpos : 0 < 4 * (1 - g) / (2 - g) ^ 2 := by
      apply div_pos <;> nlinarith
    have : 1 < Real.sqrt (1 + 4 * (1 - g) / (2 - g) ^ 2) := by
      rw [Real.lt_sqrt (by norm_num)]; linarith
    linarith

end G55DIL

open G55DIL in
theorem solution (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    (choi (sharedADC g false)).trace.re = 1 - g / 2 ∧
    conditionalChoi (sharedADC g false) = sharedChoiMatrix g ∧
    IsDensityMatrix (conditionalChoi (sharedADC g false)) ∧
    correlationTensor (conditionalChoi (sharedADC g false)) =
      Matrix.diagonal ![2 * Real.sqrt (1 - g) / (2 - g),
        -2 * Real.sqrt (1 - g) / (2 - g), 1] ∧
    IsGreatest (spatialValues (conditionalChoi (sharedADC g false)))
      (2 * Real.sqrt (1 + 4 * (1 - g) / (2 - g) ^ 2)) ∧
    (2 < 2 * Real.sqrt (1 + 4 * (1 - g) / (2 - g) ^ 2) ↔ g < 1) := by
  have h := cond_sh g hg0 hg1
  refine ⟨tr_sh g hg0 hg1, h, by rw [h]; exact dens_sh g hg0 hg1, by rw [h]; exact ctensor_sh g hg1,
    by rw [h]; exact greatest_sh g hg0 hg1, thr_sh g hg0 hg1⟩
