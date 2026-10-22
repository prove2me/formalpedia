-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P03.clockIntermediateDecomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:30:10.030071+00:00
-- url     : https://prove2.me/submissions/df76eb27-d6b7-4c4d-b6b6-9028f7c4958d

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P03
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P03

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage depolarizing)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy holevo IsLaw)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten block)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

open QAlgorithms.Papers.Independent.Claimed50.P43 (ordinaryLimit)

open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

theorem g73j_clock_entry (d : ℕ) [NeZero d] (k : Fin d) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k.val + 1 : ℕ) : ℂ) / (d : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I / d) ^ (k.val + 1) := by
  rw [← Complex.exp_nat_mul]; congr 1; ring

theorem g73j_clock_eq (d : ℕ) [NeZero d] :
    clockUnitary d = Matrix.diagonal (fun k : Fin d =>
      Complex.exp (2 * Real.pi * Complex.I / d) ^ (k.val + 1)) := by
  unfold clockUnitary; congr 1; funext k; exact g73j_clock_entry d k

theorem g73j_root_sum (d : ℕ) [NeZero d] (i j : Fin d) :
    ∑ k : Fin d, (starRingEnd ℂ (Complex.exp (2 * Real.pi * Complex.I / d) ^ (i.val + 1))) ^ (k.val + 1) *
      (Complex.exp (2 * Real.pi * Complex.I / d) ^ (j.val + 1)) ^ (k.val + 1) =
      if i = j then (d : ℂ) else 0 := by
  have hd : d ≠ 0 := NeZero.ne d
  set ζ := Complex.exp (2 * Real.pi * Complex.I / d) with hζ
  have hprim : IsPrimitiveRoot ζ d := Complex.isPrimitiveRoot_exp d hd
  have hn : ‖ζ‖ = 1 := hprim.norm'_eq_one hd
  have hne : ζ ≠ 0 := hprim.ne_zero hd
  have hconj : starRingEnd ℂ ζ = ζ⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]; simp
  set x := ζ⁻¹ ^ (i.val + 1) * ζ ^ (j.val + 1) with hx
  have hterm : ∀ k : Fin d, (starRingEnd ℂ (ζ ^ (i.val + 1))) ^ (k.val + 1) *
      (ζ ^ (j.val + 1)) ^ (k.val + 1) = x ^ (k.val + 1) := by
    intro k; rw [map_pow, hconj, hx, mul_pow]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  have hxi : x = ζ ^ j.val * (ζ ^ i.val)⁻¹ := by
    rw [hx, inv_pow, pow_succ, pow_succ]; field_simp
  rw [Fin.sum_univ_eq_sum_range (fun k => x ^ (k + 1)) d]
  split_ifs with hij
  · subst hij
    have : x = 1 := by rw [hxi]; field_simp
    simp [this]
  · have hx1 : x ≠ 1 := by
      intro h1
      rw [hxi] at h1
      have : ζ ^ j.val = ζ ^ i.val := by
        have hz : ζ ^ i.val ≠ 0 := pow_ne_zero _ hne
        field_simp at h1; exact h1
      exact hij (Fin.ext (hprim.pow_inj i.isLt j.isLt this.symm))
    have hxd : x ^ d = 1 := by
      rw [hxi, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm j.val, mul_comm i.val,
        pow_mul, pow_mul, hprim.pow_eq_one]; simp
    have hg := geom_sum_mul x d
    rw [hxd, sub_self] at hg
    have hs : ∑ k ∈ Finset.range d, x ^ k = 0 := by
      rcases mul_eq_zero.1 hg with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 h) hx1
    simp_rw [pow_succ, ← Finset.sum_mul, hs, zero_mul]

theorem g73j_depol_entry (d : ℕ) (p : ℝ) (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    QAlgorithms.Papers.Independent.Information100.P08.depolarizing d p X i j =
      ((1 - p : ℝ) : ℂ) * X i j + (p : ℂ) * X.trace * (d : ℂ)⁻¹ * (if i = j then 1 else 0) := by
  simp only [QAlgorithms.Papers.Independent.Information100.P08.depolarizing,
    QAlgorithms.Papers.Independent.Information100.P08.maximallyMixed, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, Complex.real_smul, smul_eq_mul]
  push_cast; split_ifs <;> ring

theorem g73j_inter_entry (d : ℕ) [NeZero d] (lam : ℝ) (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    intermediateChannel d lam X i j =
      QAlgorithms.Papers.Independent.Information100.P08.depolarizing d (1 - lam) X i j +
        (((1 - lam) / d : ℝ) : ℂ) * (if i = j then 0 else X i j) := by
  simp only [intermediateChannel, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.diagonal_apply, smul_eq_mul]
  split_ifs with h
  · subst h; simp
  · simp

theorem g73j_clock_sum (d : ℕ) [NeZero d] (Y : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (∑ k : Fin d, conjSuperop ((clockUnitary d ^ (k.val + 1))ᴴ) Y) i j =
      Y i j * (if i = j then (d : ℂ) else 0) := by
  rw [Matrix.sum_apply]
  have h : ∀ k : Fin d, conjSuperop ((clockUnitary d ^ (k.val + 1))ᴴ) Y i j =
      Y i j * ((starRingEnd ℂ (Complex.exp (2 * Real.pi * Complex.I / d) ^ (i.val + 1))) ^ (k.val + 1) *
      (Complex.exp (2 * Real.pi * Complex.I / d) ^ (j.val + 1)) ^ (k.val + 1)) := by
    intro k
    simp only [conjSuperop, g73j_clock_eq, Matrix.diagonal_pow, Matrix.diagonal_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.pow_apply,
      Pi.star_apply, RCLike.star_def, map_pow, Complex.conj_conj]
    ring
  rw [Finset.sum_congr rfl (fun k _ => h k), ← Finset.mul_sum, g73j_root_sum]


/-- King quant-ph/0204172v2, PDF p.13, Lemma 10, (49).
All-operator linear extensions; the default interval gives D>0.
This algebraic identity does not assert that its coefficients are nonnegative. -/
theorem solution {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (lam : ℝ) (hlow : -1 / ((d : ℝ)^2 - 1) ≤ lam) (hhigh : lam ≤ 1)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    depolarizing d (1 - lam) X =
      (((lam * d / (1 + ((d : ℝ) - 1) * lam)) : ℝ) : ℂ) • intermediateChannel d lam X +
      ((((1 - lam) / ((1 + ((d : ℝ) - 1) * lam) * d)) : ℝ) : ℂ) •
        ∑ k : Fin d, conjSuperop ((clockUnitary d ^ (k.val + 1))ᴴ) (intermediateChannel d lam X) := by
  have hd1 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hD : 0 < 1 + ((d : ℝ) - 1) * lam := by
    have h1 : (0 : ℝ) < (d : ℝ)^2 - 1 := by nlinarith
    have : -1 ≤ lam * ((d : ℝ)^2 - 1) := by
      rw [div_le_iff₀ h1] at hlow; linarith
    nlinarith
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  have hDC : ((1 + ((d : ℝ) - 1) * lam : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, g73j_clock_sum, g73j_inter_entry,
    g73j_depol_entry]
  push_cast at hDC ⊢
  have h2 : (1 + (d:ℂ) * lam - lam) ≠ 0 := by intro h; apply hDC; linear_combination h
  have h3 : (1 - (lam:ℂ) + lam * d) ≠ 0 := by intro h; apply hDC; linear_combination h
  split_ifs with h
  · field_simp; ring_nf; field_simp; ring
  · field_simp; ring_nf; field_simp; ring



end
