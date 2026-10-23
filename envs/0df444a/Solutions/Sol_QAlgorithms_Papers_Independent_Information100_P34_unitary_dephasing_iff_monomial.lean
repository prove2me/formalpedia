-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P34.unitary_dephasing_iff_monomial
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:28:42.681785+00:00
-- url     : https://prove2.me/submissions/bdee9ca9-1ef5-4aa8-be56-6d138bdc15ba

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P34

private lemma x8_conj_apply {d : ℕ} (A M : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (A * M * Aᴴ) i j = ∑ a, ∑ b, A i a * M a b * star (A j b) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

private lemma x8_single_conj {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (k i j : Fin d) :
    (A * Matrix.single k k (1 : ℂ) * Aᴴ) i j = A i k * star (A j k) := by
  rw [x8_conj_apply]
  simp [Matrix.single_apply, ite_and]

private lemma x8_dephasing_single {d : ℕ} (k : Fin d) :
    dephasing (Matrix.single k k (1 : ℂ)) = Matrix.single k k (1 : ℂ) := by
  ext i j
  simp only [dephasing, Matrix.diagonal_apply, Matrix.single_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]; intro h1 h2; exact hij (h1 ▸ h2)

/-- For `A i a = [i = π a] ω a`, conjugation permutes and rescales entries. -/
private lemma x8_monomial_conj {d : ℕ} (pi : Equiv.Perm (Fin d)) (omega : Fin d → ℂ)
    (M : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    ((permutationMatrix pi * Matrix.diagonal omega) * M *
        (permutationMatrix pi * Matrix.diagonal omega)ᴴ) i j =
      omega (pi.symm i) * M (pi.symm i) (pi.symm j) * star (omega (pi.symm j)) := by
  have hA : ∀ i a, (permutationMatrix pi * Matrix.diagonal omega) i a =
      if a = pi.symm i then omega a else 0 := by
    intro i a
    rw [Matrix.mul_diagonal]
    simp only [permutationMatrix]
    by_cases h : a = pi.symm i
    · subst h; simp
    · have h' : ¬ i = pi a := by
        intro h''; apply h; rw [h'', Equiv.symm_apply_apply]
      simp [h, h']
  rw [x8_conj_apply]
  simp only [hA]
  simp [ite_mul, mul_ite, apply_ite (starRingEnd ℂ), Finset.sum_ite_eq']

theorem x8_main {d : ℕ} (hd : 0 < d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (∀ X : Matrix (Fin d) (Fin d) ℂ,
      conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) (dephasing X) =
        dephasing (conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) X)) ↔
    ∃ pi : Equiv.Perm (Fin d), ∃ omega : Fin d → ℂ,
      (∀ k, ‖omega k‖ = 1) ∧
      (U : Matrix (Fin d) (Fin d) ℂ) = permutationMatrix pi * Matrix.diagonal omega := by
  set A : Matrix (Fin d) (Fin d) ℂ := (U : Matrix (Fin d) (Fin d) ℂ) with hAdef
  have hU : star A * A = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have hcol : ∀ k l, ∑ i, star (A i k) * A i l = if k = l then 1 else 0 := by
    intro k l
    have := congrFun (congrFun hU k) l
    rw [Matrix.mul_apply] at this
    simpa [Matrix.one_apply, Matrix.star_apply] using this
  constructor
  · intro h
    -- off-diagonal products in a column vanish
    have hoff : ∀ k i j, i ≠ j → A i k * star (A j k) = 0 := by
      intro k i j hij
      have := congrFun (congrFun (h (Matrix.single k k 1)) i) j
      simp only [conjSuperop] at this
      rw [x8_dephasing_single, x8_single_conj] at this
      rw [this]
      simp [dephasing, Matrix.diagonal_apply, hij]
    have hex : ∀ k, ∃ i, A i k ≠ 0 := by
      intro k
      by_contra hcon
      push Not at hcon
      have := hcol k k
      simp [hcon] at this
    choose p hp using hex
    have hzero : ∀ k i, i ≠ p k → A i k = 0 := by
      intro k i hi
      have := hoff k i (p k) hi
      rcases mul_eq_zero.mp this with h1 | h1
      · exact h1
      · exact absurd (star_eq_zero.mp h1) (hp k)
    have hnorm : ∀ k, star (A (p k) k) * A (p k) k = 1 := by
      intro k
      have := hcol k k
      rw [if_pos rfl, Finset.sum_eq_single (p k)] at this
      · exact this
      · intro i _ hi; rw [hzero k i hi]; simp
      · simp
    have hinj : Function.Injective p := by
      intro k l hkl
      by_contra hne
      have := hcol k l
      rw [if_neg hne, Finset.sum_eq_single (p k)] at this
      · rw [hkl] at this
        have h1 : star (A (p l) k) ≠ 0 := by
          rw [← hkl]; exact star_ne_zero.mpr (hp k)
        exact mul_ne_zero h1 (hp l) this
      · intro i _ hi; rw [hzero k i hi]; simp
      · simp
    let pi : Equiv.Perm (Fin d) := Equiv.ofBijective p (Finite.injective_iff_bijective.mp hinj)
    refine ⟨pi, fun k => A (p k) k, fun k => ?_, ?_⟩
    · have h1 := hnorm k
      have h2 : ((‖A (p k) k‖ : ℂ)) ^ 2 = 1 := by
        rw [← Complex.conj_mul', ← h1]; rfl
      have h3 : ‖A (p k) k‖ ^ 2 = 1 := by exact_mod_cast h2
      have h4 : 0 ≤ ‖A (p k) k‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖A (p k) k‖ - 1), sq_nonneg (‖A (p k) k‖ + 1)]
    · ext i j
      rw [Matrix.mul_diagonal]
      simp only [permutationMatrix]
      by_cases hij : i = p j
      · have : i = pi j := hij
        rw [if_pos this, hij, one_mul]
      · have : ¬ i = pi j := hij
        rw [if_neg this, zero_mul]
        exact hzero j i hij
  · rintro ⟨pi, omega, hom, hAe⟩ X
    simp only [conjSuperop]
    rw [hAe]
    ext i j
    rw [x8_monomial_conj]
    simp only [dephasing, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl, x8_monomial_conj]
    · have : pi.symm i ≠ pi.symm j := fun h => hij (pi.symm.injective h)
      rw [if_neg this, if_neg hij]; simp

end QAlgorithms.Papers.Independent.Information100.P34

end

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P34 in
theorem solution {d : ℕ} (hd : 0 < d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (∀ X : Matrix (Fin d) (Fin d) ℂ,
      conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) (dephasing X) =
        dephasing (conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) X)) ↔
    ∃ pi : Equiv.Perm (Fin d), ∃ omega : Fin d → ℂ,
      (∀ k, ‖omega k‖ = 1) ∧
      (U : Matrix (Fin d) (Fin d) ℂ) = permutationMatrix pi * Matrix.diagonal omega :=
  x8_main hd U
