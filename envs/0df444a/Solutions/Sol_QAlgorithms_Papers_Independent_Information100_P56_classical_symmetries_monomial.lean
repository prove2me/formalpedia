-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P56.classical_symmetries_monomial
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T05:54:13.648388+00:00
-- url     : https://prove2.me/submissions/b7881fec-9e7d-45bd-9c6c-58a31e4ba2e4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

theorem solution
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (U : Matrix.unitaryGroup X ℂ)
    (hdiag : Set.image (fun D : Matrix X X ℂ => (U : Matrix X X ℂ) * D * (U : Matrix X X ℂ)ᴴ)
      (Set.range (Matrix.diagonal : (X → ℂ) → Matrix X X ℂ)) =
        Set.range (Matrix.diagonal : (X → ℂ) → Matrix X X ℂ)) :
    ∃ (pi : Equiv.Perm X) (theta : X → ℝ),
      (∀ i j, (U : Matrix X X ℂ) i j =
        if i = pi j then Complex.exp ((theta j : ℂ) * Complex.I) else 0) ∧
      (∀ p : X → ℂ,
        (U : Matrix X X ℂ) * Matrix.diagonal p * (U : Matrix X X ℂ)ᴴ =
          Matrix.diagonal (fun i => p (pi.symm i))) := by
  set W : Matrix X X ℂ := (U : Matrix X X ℂ) with hW
  have hWW : Wᴴ * W = 1 := Unitary.star_mul_self_of_mem U.2
  have hmem : ∀ d : X → ℂ, ∃ e, W * Matrix.diagonal d * Wᴴ = Matrix.diagonal e := by
    intro d
    have : W * Matrix.diagonal d * Wᴴ ∈ Set.range (Matrix.diagonal : (X → ℂ) → Matrix X X ℂ) := by
      rw [← hdiag]; exact ⟨Matrix.diagonal d, ⟨d, rfl⟩, rfl⟩
    obtain ⟨e, he⟩ := this
    exact ⟨e, he.symm⟩
  -- off-diagonal products vanish
  have hoff : ∀ j i k, i ≠ k → W i j * star (W k j) = 0 := by
    intro j i k hik
    obtain ⟨e, he⟩ := hmem (fun l => if l = j then 1 else 0)
    have := congrFun (congrFun he i) k
    rw [Matrix.diagonal_apply_ne _ hik] at this
    simpa [Matrix.mul_apply, Matrix.diagonal_apply] using this
  have hcol : ∀ j, ∑ i, star (W i j) * W i j = 1 := by
    intro j
    have := congrFun (congrFun hWW j) j
    simpa [Matrix.mul_apply] using this
  have hex : ∀ j, ∃ i, W i j ≠ 0 := by
    intro j
    by_contra h
    push Not at h
    have := hcol j
    simp [h] at this
  choose pf hpf using hex
  have hzero : ∀ j i, i ≠ pf j → W i j = 0 := by
    intro j i hi
    have := hoff j i (pf j) hi
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd (star_eq_zero.mp h) (hpf j)
  have hinj : Function.Injective pf := by
    intro j j' h
    by_contra hjj
    have := congrFun (congrFun hWW j) j'
    rw [Matrix.one_apply_ne hjj, Matrix.mul_apply] at this
    rw [Finset.sum_eq_single (pf j)] at this
    · simp only [Matrix.conjTranspose_apply] at this
      rcases mul_eq_zero.mp this with h1 | h1
      · exact hpf j (star_eq_zero.mp h1)
      · exact hpf j' (h ▸ h1)
    · intro b _ hb
      simp [hzero j b hb]
    · simp
  have hbij : Function.Bijective pf := Finite.injective_iff_bijective.mp hinj
  let pi : Equiv.Perm X := Equiv.ofBijective pf hbij
  have hpi : ∀ j, pi j = pf j := fun j => rfl
  have hnorm : ∀ j, ‖W (pf j) j‖ = 1 := by
    intro j
    have := hcol j
    rw [Finset.sum_eq_single (pf j)] at this
    · have h2 : star (W (pf j) j) * W (pf j) j = ((‖W (pf j) j‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [h2] at this
      have h3 : ‖W (pf j) j‖ ^ 2 = 1 := by exact_mod_cast this
      have h4 := norm_nonneg (W (pf j) j)
      nlinarith
    · intro b _ hb; simp [hzero j b hb]
    · simp
  have hform : ∀ i j, W i j = if i = pi j then Complex.exp ((Complex.arg (W (pf j) j) : ℂ) * Complex.I) else 0 := by
    intro i j
    rw [hpi]
    split_ifs with h
    · subst h
      have := Complex.norm_mul_exp_arg_mul_I (W (pf j) j)
      rw [hnorm j] at this
      simpa using this.symm
    · exact hzero j i h
  refine ⟨pi, fun j => Complex.arg (W (pf j) j), hform, ?_⟩
  intro p
  ext i k
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single (pi.symm i)]
  · have hi : pi (pi.symm i) = i := pi.apply_symm_apply i
    by_cases hik : i = k
    · subst hik
      rw [Matrix.diagonal_apply_eq]
      have hn := hnorm (pi.symm i)
      rw [← hpi, hi] at hn
      have : W i (pi.symm i) * star (W i (pi.symm i)) = 1 := by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
      calc W i (pi.symm i) * p (pi.symm i) * star (W i (pi.symm i))
          = p (pi.symm i) * (W i (pi.symm i) * star (W i (pi.symm i))) := by ring
        _ = p (pi.symm i) := by rw [this, mul_one]
    · rw [Matrix.diagonal_apply_ne _ hik]
      have : W k (pi.symm i) = 0 := hzero _ k (by rw [← hpi, hi]; exact Ne.symm hik)
      simp [this]
  · intro b _ hb
    have : W i b = 0 := hzero b i (by
      rw [← hpi]; intro h; apply hb; rw [h]; simp)
    simp [this]
  · simp

end
