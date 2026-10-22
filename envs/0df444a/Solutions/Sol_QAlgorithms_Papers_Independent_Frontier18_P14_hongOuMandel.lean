-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P14.hongOuMandel
-- status  : ACCEPTED   (prove)
-- author  : @Yonghao Wang
-- created : 2026-10-21T07:04:56.731128+00:00
-- url     : https://prove2.me/submissions/e6246ad1-26a5-4601-8117-922563989a5a

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

open Filter

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Frontier18.P14
open QAlgorithms.Papers.Independent.Dependency50.P34 (fockKet fockOutput)

namespace HomAux

/-- The balanced-splitter amplitude `1/√2`. -/
def homC : ℂ := 1 / (Real.sqrt 2 : ℂ)

lemma homC_eq : homC = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by
  rw [homC]
  push_cast
  norm_num

lemma sqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma sqrt2_ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  intro h
  have h2 := sqrt2_sq
  rw [h, zero_mul] at h2
  norm_num at h2

lemma normSq_homC : Complex.normSq homC = (1 / 2 : ℝ) := by
  rw [homC_eq, Complex.normSq_ofReal, div_mul_div_comm, one_mul,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

lemma norm_homC_sq : ‖homC‖ ^ 2 = (1 / 2 : ℝ) := by
  rw [← Complex.normSq_eq_norm_sq, normSq_homC]

/-- The Hong–Ou–Mandel output vector `(|2,0⟩ - |0,2⟩)/√2`. -/
def homOut : Fock := homC • (fockKet 2 0 - fockKet 0 2)

lemma homOut_apply (pq : ℕ × ℕ) :
    homOut pq = if pq = (2, 0) then homC else if pq = (0, 2) then -homC else 0 := by
  have h12 : (2, 0) ≠ (0, 2) := by norm_num
  have h21 : (0, 2) ≠ (2, 0) := by norm_num
  simp only [homOut, lp.coeFn_smul, Pi.smul_apply, lp.coeFn_sub, Pi.sub_apply]
  by_cases h1 : pq = (2, 0)
  · subst h1
    simp [fockKet, h12]
  · by_cases h2 : pq = (0, 2)
    · subst h2
      simp [fockKet, h1, h21]
    · simp [fockKet, h1, h2, h12, h21]

/-! ### Coordinates of the output of the creation polynomial -/

lemma balanced_00 : balanced 0 0 = 1 / (Real.sqrt 2 : ℂ) := rfl
lemma balanced_01 : balanced 0 1 = 1 / (Real.sqrt 2 : ℂ) := rfl
lemma balanced_10 : balanced 1 0 = -(1 / (Real.sqrt 2 : ℂ)) := rfl
lemma balanced_11 : balanced 1 1 = 1 / (Real.sqrt 2 : ℂ) := rfl

lemma fockOutput_balanced_20 : fockOutput balanced 1 1 (2, 0) = homC := by
  rw [fockOutput, homC]
  simp only [lp.coeFn_sum, lp.coeFn_smul, Finset.sum_apply, Pi.smul_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_zero, zero_add]
  rw [balanced_00, balanced_01, balanced_10, balanced_11]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := sqrt2_ne
  simp [fockKet]
  try field_simp
  try ring

lemma fockOutput_balanced_02 : fockOutput balanced 1 1 (0, 2) = -homC := by
  rw [fockOutput, homC]
  simp only [lp.coeFn_sum, lp.coeFn_smul, Finset.sum_apply, Pi.smul_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_zero, zero_add]
  rw [balanced_00, balanced_01, balanced_10, balanced_11]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := sqrt2_ne
  simp [fockKet]
  try field_simp
  try ring

lemma fockOutput_balanced_11 : fockOutput balanced 1 1 (1, 1) = 0 := by
  rw [fockOutput]
  simp only [lp.coeFn_sum, lp.coeFn_smul, Finset.sum_apply, Pi.smul_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_zero, zero_add]
  rw [balanced_00, balanced_01, balanced_10, balanced_11]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := sqrt2_ne
  simp [fockKet]
  try field_simp
  try ring

lemma fockOutput_balanced_other (pq : ℕ × ℕ) (h1 : pq ≠ (2, 0)) (h2 : pq ≠ (0, 2))
    (h3 : pq ≠ (1, 1)) : fockOutput balanced 1 1 pq = 0 := by
  rw [fockOutput]
  simp only [lp.coeFn_sum, lp.coeFn_smul, Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  apply Finset.sum_eq_zero
  intro l hl
  have hk2 : k = 0 ∨ k = 1 := by
    have hklt : k < 2 := Finset.mem_range.mp hk
    omega
  have hl2 : l = 0 ∨ l = 1 := by
    have hllt : l < 2 := Finset.mem_range.mp hl
    omega
  rcases hk2 with rfl | rfl <;> rcases hl2 with rfl | rfl <;>
    simp [fockKet, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3]

lemma fockOutput_balanced_apply (pq : ℕ × ℕ) :
    fockOutput balanced 1 1 pq = homOut pq := by
  rw [homOut_apply]
  by_cases h1 : pq = (2, 0)
  · subst h1
    rw [if_pos rfl]
    exact fockOutput_balanced_20
  · rw [if_neg h1]
    by_cases h2 : pq = (0, 2)
    · subst h2
      rw [if_pos rfl]
      exact fockOutput_balanced_02
    · rw [if_neg h2]
      by_cases h3 : pq = (1, 1)
      · subst h3
        exact fockOutput_balanced_11
      · exact fockOutput_balanced_other pq h1 h2 h3

/-! ### The passive coefficient array of `|1,1⟩` -/

lemma passiveCoefficients_apply (pq : ℕ × ℕ) :
    passiveCoefficients balanced (fockKet 1 1) pq = homOut pq := by
  unfold passiveCoefficients
  rw [Finset.sum_eq_single 1]
  · by_cases hK : pq.1 + pq.2 = 2
    · have hsub : pq.1 + pq.2 - 1 = 1 := by omega
      rw [hsub]
      have hk : fockKet 1 1 (1, 1) = 1 := by simp [fockKet]
      rw [hk, one_mul]
      exact fockOutput_balanced_apply pq
    · have hsub : pq.1 + pq.2 - 1 ≠ 1 := by omega
      have hk : fockKet 1 1 (1, pq.1 + pq.2 - 1) = 0 := by simp [fockKet, hsub]
      rw [hk, zero_mul, homOut_apply]
      have hp1 : pq ≠ (2, 0) := by
        rintro rfl
        exact hK (by norm_num)
      have hp2 : pq ≠ (0, 2) := by
        rintro rfl
        exact hK (by norm_num)
      rw [if_neg hp1, if_neg hp2]
  · intro m hm hne
    have hne' : (m, pq.1 + pq.2 - m) ≠ (1, 1) := by
      intro h
      exact hne (by simpa using congrArg Prod.fst h)
    simp [fockKet, hne', Ne.symm hne']
  · intro hmem
    have hlt : ¬ (1 < pq.1 + pq.2 + 1) := by
      simpa [Finset.mem_range] using hmem
    have h0 : pq.1 + pq.2 = 0 := by omega
    have hk : fockKet 1 1 (1, pq.1 + pq.2 - 1) = 0 := by
      rw [h0]
      simp [fockKet]
    rw [hk, zero_mul]

lemma passiveApply_eq : passiveApply balanced (fockKet 1 1) = homOut := by
  have hfun : passiveCoefficients balanced (fockKet 1 1) = ⇑homOut := by
    funext pq
    exact passiveCoefficients_apply pq
  have hmem : Memℓp (passiveCoefficients balanced (fockKet 1 1)) 2 := by
    rw [hfun]
    exact homOut.2
  unfold passiveApply
  rw [dif_pos hmem]
  exact Subtype.ext hfun

/-! ### Norm and joint detection probabilities -/

lemma single_eq_smul (i : ℕ × ℕ) (c : ℂ) :
    lp.single (E := fun _ : ℕ × ℕ => ℂ) 2 i c =
      c • lp.single (E := fun _ : ℕ × ℕ => ℂ) 2 i (1 : ℂ) := by
  rw [← lp.single_smul, smul_eq_mul, mul_one]

lemma homOut_sum :
    homOut = ∑ i ∈ ({(2, 0), (0, 2)} : Finset (ℕ × ℕ)),
      lp.single 2 i (if i = (2, 0) then homC else -homC) := by
  rw [Finset.sum_insert (by simp : (2, 0) ∉ ({(0, 2)} : Finset (ℕ × ℕ))), Finset.sum_singleton,
    if_pos rfl, if_neg (by norm_num : ¬ ((0, 2) = (2, 0)))]
  simp only [homOut, fockKet]
  rw [smul_sub, ← single_eq_smul, ← single_eq_smul, lp.single_neg, sub_eq_add_neg]

lemma homOut_norm : ‖homOut‖ = 1 := by
  have hsum := homOut_sum
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have h := lp.norm_sum_single (p := (2 : ℝ≥0∞))
    (E := fun _ : ℕ × ℕ => ℂ) hp
    (fun i : ℕ × ℕ => if i = (2, 0) then homC else -homC) ({(2, 0), (0, 2)} : Finset (ℕ × ℕ))
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [← hsum] at h
  rw [Finset.sum_insert (by simp : (2, 0) ∉ ({(0, 2)} : Finset (ℕ × ℕ))),
    Finset.sum_singleton] at h
  rw [if_pos rfl, if_neg (by norm_num : ¬ ((0, 2) = (2, 0))), norm_neg, norm_homC_sq] at h
  have h1 : ‖homOut‖ ^ 2 = 1 := by
    rw [h]
    norm_num
  nlinarith [norm_nonneg homOut]

lemma homOut_normSq (mn : ℕ × ℕ) :
    Complex.normSq (homOut mn) =
      if mn = (2, 0) ∨ mn = (0, 2) then (1 / 2 : ℝ) else 0 := by
  rw [homOut_apply]
  by_cases h1 : mn = (2, 0)
  · subst h1
    rw [if_pos rfl, if_pos (Or.inl rfl), normSq_homC]
  · rw [if_neg h1]
    by_cases h2 : mn = (0, 2)
    · subst h2
      rw [if_pos rfl, if_pos (Or.inr rfl), Complex.normSq_neg, normSq_homC]
    · rw [if_neg h2, if_neg (by tauto : ¬ (mn = (2, 0) ∨ mn = (0, 2)))]
      simp

end HomAux

theorem solution :
    passiveApply balanced (fockKet 1 1) =
      (1 / (Real.sqrt 2 : ℂ)) • (fockKet 2 0 - fockKet 0 2) ∧
    ‖passiveApply balanced (fockKet 1 1)‖ = 1 ∧
    (∀ mn : ℕ × ℕ, Complex.normSq (passiveApply balanced (fockKet 1 1) mn) =
      if mn = (2, 0) ∨ mn = (0, 2) then (1 / 2 : ℝ) else 0) := by
  have hpa : passiveApply balanced (fockKet 1 1) = HomAux.homOut := HomAux.passiveApply_eq
  refine ⟨hpa, ?_, ?_⟩
  · rw [hpa]
    exact HomAux.homOut_norm
  · intro mn
    rw [hpa]
    exact HomAux.homOut_normSq mn
