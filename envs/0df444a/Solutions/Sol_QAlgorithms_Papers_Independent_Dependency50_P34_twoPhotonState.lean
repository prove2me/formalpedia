-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P34.twoPhotonState
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:05:44.409982+00:00
-- url     : https://prove2.me/submissions/09f8fd11-756f-4c0c-880f-7444aec482f2

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P34

noncomputable section

open scoped Matrix

namespace QAlgorithms.Papers.Independent.Dependency50.P34

lemma X7_sqrt2_sq : ((Real.sqrt 2 : ℂ)) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

lemma X7_sqrt2_ne : ((Real.sqrt 2 : ℂ)) ≠ 0 := by
  have : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  exact_mod_cast this.ne'

lemma X7_mzi_entries (theta : ℝ) :
    mziMatrix balancedSplitter balancedSplitter theta 0 0 = (1 - Complex.exp (Complex.I * (theta : ℂ))) / 2 ∧
    mziMatrix balancedSplitter balancedSplitter theta 1 0 = Complex.I * (1 + Complex.exp (Complex.I * (theta : ℂ))) / 2 ∧
    mziMatrix balancedSplitter balancedSplitter theta 0 1 = Complex.I * (1 + Complex.exp (Complex.I * (theta : ℂ))) / 2 ∧
    mziMatrix balancedSplitter balancedSplitter theta 1 1 = (Complex.exp (Complex.I * (theta : ℂ)) - 1) / 2 := by
  have h2 := X7_sqrt2_sq
  have hne := X7_sqrt2_ne
  simp only [mziMatrix, balancedSplitter, beamMatrix, phaseMatrix, Matrix.mul_apply,
    Fin.sum_univ_two]
  simp
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> rw [h2] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

lemma X7_output_expand (theta : ℝ) :
    comparisonOutput theta =
      ((Real.sqrt 2 : ℂ) * mziMatrix balancedSplitter balancedSplitter theta 1 0 *
        mziMatrix balancedSplitter balancedSplitter theta 1 1) • fockKet 0 2 +
      (mziMatrix balancedSplitter balancedSplitter theta 1 0 *
        mziMatrix balancedSplitter balancedSplitter theta 0 1) • fockKet 1 1 +
      (mziMatrix balancedSplitter balancedSplitter theta 0 0 *
        mziMatrix balancedSplitter balancedSplitter theta 1 1) • fockKet 1 1 +
      ((Real.sqrt 2 : ℂ) * mziMatrix balancedSplitter balancedSplitter theta 0 0 *
        mziMatrix balancedSplitter balancedSplitter theta 0 1) • fockKet 2 0 := by
  simp [comparisonOutput, fockOutput, Finset.sum_range_succ, Nat.factorial]
  rw [show (1:ℝ) + 1 = 2 by norm_num]
  abel

lemma X7_exp2 (theta : ℝ) :
    Complex.exp (2 * Complex.I * (theta : ℂ)) = Complex.exp (Complex.I * (theta : ℂ)) ^ 2 := by
  rw [sq, ← Complex.exp_add]; ring_nf

lemma X7_state (theta : ℝ) :
    let e := Complex.exp (2 * Complex.I * (theta : ℂ))
    comparisonOutput theta =
        (Complex.I * (1 - e) / (2 * (Real.sqrt 2 : ℂ))) •
          (fockKet 2 0 - fockKet 0 2) -
        ((1 + e) / 2) • fockKet 1 1 := by
  intro e
  obtain ⟨h00, h10, h01, h11⟩ := X7_mzi_entries theta
  rw [X7_output_expand, h00, h10, h01, h11]
  simp only [e, X7_exp2]
  have h2 := X7_sqrt2_sq
  have hne := X7_sqrt2_ne
  set w := Complex.exp (Complex.I * (theta : ℂ))
  rw [smul_sub]
  match_scalars <;> field_simp <;> ring_nf <;> (try simp only [Complex.I_sq, h2]) <;> ring_nf

/-- the two key coefficients in real form -/
lemma X7_a_form (theta : ℝ) :
    Complex.I * (1 - Complex.exp (2 * Complex.I * (theta : ℂ))) / (2 * (Real.sqrt 2 : ℂ)) =
      ((Real.sin theta * Real.cos theta / Real.sqrt 2 : ℝ) : ℂ) +
        ((Real.sin theta ^ 2 / Real.sqrt 2 : ℝ) : ℂ) * Complex.I := by
  have hne := X7_sqrt2_ne
  have hE : Complex.exp (2 * Complex.I * (theta : ℂ)) =
      ((Real.cos (2 * theta) : ℝ) : ℂ) + ((Real.sin (2 * theta) : ℝ) : ℂ) * Complex.I := by
    rw [show 2 * Complex.I * (theta : ℂ) = ((2 * theta : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hE, Real.cos_two_mul, Real.sin_two_mul]
  have hcs := Complex.sin_sq_add_cos_sq (theta : ℂ)
  push_cast
  field_simp
  linear_combination (-2 * Complex.I) * hcs + (-2 * Complex.cos (theta : ℂ) * Complex.sin (theta : ℂ)) * Complex.I_sq

lemma X7_b_form (theta : ℝ) :
    (1 + Complex.exp (2 * Complex.I * (theta : ℂ))) / 2 =
      ((Real.cos theta ^ 2 : ℝ) : ℂ) + ((Real.sin theta * Real.cos theta : ℝ) : ℂ) * Complex.I := by
  have hE : Complex.exp (2 * Complex.I * (theta : ℂ)) =
      ((Real.cos (2 * theta) : ℝ) : ℂ) + ((Real.sin (2 * theta) : ℝ) : ℂ) * Complex.I := by
    rw [show 2 * Complex.I * (theta : ℂ) = ((2 * theta : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hE, Real.cos_two_mul, Real.sin_two_mul]
  push_cast
  ring

lemma X7_normSq_a (theta : ℝ) :
    Complex.normSq (Complex.I * (1 - Complex.exp (2 * Complex.I * (theta : ℂ))) /
      (2 * (Real.sqrt 2 : ℂ))) = (1 / 2 : ℝ) * Real.sin theta ^ 2 := by
  rw [X7_a_form, Complex.normSq_add_mul_I]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  have hcs := Real.sin_sq_add_cos_sq theta
  field_simp
  rw [h2]
  linear_combination (2 * Real.sin theta ^ 2) * hcs

lemma X7_normSq_b (theta : ℝ) :
    Complex.normSq ((1 + Complex.exp (2 * Complex.I * (theta : ℂ))) / 2) = Real.cos theta ^ 2 := by
  rw [X7_b_form, Complex.normSq_add_mul_I]
  have hcs := Real.sin_sq_add_cos_sq theta
  linear_combination (Real.cos theta ^ 2) * hcs

lemma X7_coord (theta : ℝ) (nm : ℕ × ℕ) :
    comparisonOutput theta nm =
      (if nm = (2, 0) then Complex.I * (1 - Complex.exp (2 * Complex.I * (theta : ℂ))) /
          (2 * (Real.sqrt 2 : ℂ)) else 0) -
      (if nm = (0, 2) then Complex.I * (1 - Complex.exp (2 * Complex.I * (theta : ℂ))) /
          (2 * (Real.sqrt 2 : ℂ)) else 0) -
      (if nm = (1, 1) then (1 + Complex.exp (2 * Complex.I * (theta : ℂ))) / 2 else 0) := by
  rw [X7_state]
  simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, fockKet, lp.single_apply,
    smul_eq_mul]
  simp only [Pi.single_apply]
  split_ifs <;> simp_all

lemma X7_c20 (theta : ℝ) : comparisonOutput theta (2, 0) =
    Complex.I * (1 - Complex.exp (2 * Complex.I * (theta : ℂ))) / (2 * (Real.sqrt 2 : ℂ)) := by
  rw [X7_coord]; simp

lemma X7_c02 (theta : ℝ) : comparisonOutput theta (0, 2) =
    -(Complex.I * (1 - Complex.exp (2 * Complex.I * (theta : ℂ))) / (2 * (Real.sqrt 2 : ℂ))) := by
  rw [X7_coord]; simp

lemma X7_c11 (theta : ℝ) : comparisonOutput theta (1, 1) =
    -((1 + Complex.exp (2 * Complex.I * (theta : ℂ))) / 2) := by
  rw [X7_coord]; simp

lemma X7_support (theta : ℝ) (nm : ℕ × ℕ)
    (h : nm ∉ ({(2, 0), (1, 1), (0, 2)} : Finset (ℕ × ℕ))) : comparisonOutput theta nm = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [X7_coord]; simp [h1, h2, h3]

lemma X7_tsum (theta : ℝ) (F : ℕ × ℕ → ℝ)
    (hF : ∀ nm, comparisonOutput theta nm = 0 → F nm = 0) :
    Summable F ∧ ∑' nm, F nm = F (2, 0) + F (1, 1) + F (0, 2) := by
  have hz : ∀ nm ∉ ({(2, 0), (1, 1), (0, 2)} : Finset (ℕ × ℕ)), F nm = 0 :=
    fun nm h => hF nm (X7_support theta nm h)
  refine ⟨summable_of_ne_finset_zero hz, ?_⟩
  rw [tsum_eq_sum hz]
  simp [Finset.sum_insert]
  ring

lemma X7_norm (theta : ℝ) : ‖comparisonOutput theta‖ = 1 := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have h := lp.norm_rpow_eq_tsum hp (comparisonOutput theta)
  obtain ⟨-, ht⟩ := X7_tsum theta (fun i => ‖comparisonOutput theta i‖ ^ (2 : ENNReal).toReal)
    (fun nm h0 => by simp [h0])
  rw [ht] at h
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Complex.sq_norm, X7_c20, X7_c02, X7_c11,
    Complex.normSq_neg, X7_normSq_a, X7_normSq_b] at h
  have hcs := Real.sin_sq_add_cos_sq theta
  have h1 : ‖comparisonOutput theta‖ ^ 2 = 1 := by rw [h]; linarith
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h1

end QAlgorithms.Papers.Independent.Dependency50.P34

open QAlgorithms.Papers.Independent.Dependency50.P34 in
theorem solution (theta : ℝ) :
    let e := Complex.exp (2 * Complex.I * (theta : ℂ))
    ‖comparisonOutput theta‖ = 1 ∧
      comparisonOutput theta =
        (Complex.I * (1 - e) / (2 * (Real.sqrt 2 : ℂ))) •
          (fockKet 2 0 - fockKet 0 2) -
        ((1 + e) / 2) • fockKet 1 1 := by
  intro e
  exact ⟨X7_norm theta, X7_state theta⟩

end
