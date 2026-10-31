-- Prove2me | solution 1 for QAlgorithms.Nannicini.eigvec_eq_smul_of_hasGapAround
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-30T14:35:04.593144+00:00
-- url     : https://prove2.me/submissions/b0a8193d-514b-40d0-aff5-0ad87e390e68

import Definitions.Def_QAlgorithms_Defs_Adiabatic

set_option autoImplicit false

open QAlgorithms

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (lam γ : ℝ) (hA : HasGapAround A lam γ) (x y : EuclideanSpace ℂ ι)
    (hx : IsState x) (hy : IsState y) (hAx : act A x = (lam : ℂ) • x)
    (hAy : act A y = (lam : ℂ) • y) : ∃ ω : ℂ, ‖ω‖ = 1 ∧ y = ω • x := by
  obtain ⟨hH, ⟨k0, hk0, huniq⟩, -⟩ := hA
  set b := hH.eigenvectorBasis with hbdef
  have hsym : (Matrix.toEuclideanLin A).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  -- `λ` is attained by exactly one index of `hH.eigenvalues`
  have hev : ∀ i j : ι, hH.eigenvalues i = lam → hH.eigenvalues j = lam → i = j := by
    intro i j hi hj
    have key : ∀ i, hH.eigenvalues i = lam →
        Fin.rev ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm i) = k0 := by
      intro i hi
      apply huniq
      simp only [ascEigenvalues, dif_pos hH, Fin.rev_rev]
      exact hi
    have := (key i hi).trans (key j hj).symm
    simpa using this
  have hb : ∀ i, Matrix.toEuclideanLin A (b i) = (hH.eigenvalues i : ℂ) • b i := by
    intro i
    rw [Matrix.toEuclideanLin_apply, hbdef, hH.mulVec_eigenvectorBasis]
    ext j
    simp [RCLike.real_smul_eq_coe_mul]
  have hcoef : ∀ z : EuclideanSpace ℂ ι, act A z = (lam : ℂ) • z →
      ∀ i, hH.eigenvalues i ≠ lam → inner ℂ (b i) z = 0 := by
    intro z hz i hi
    have h1 : inner ℂ (b i) (act A z) = (hH.eigenvalues i : ℂ) * inner ℂ (b i) z := by
      have hact : act A z = Matrix.toEuclideanLin A z := rfl
      rw [hact, ← hsym (b i) z, hb i, inner_smul_left]
      simp
    rw [hz, inner_smul_right] at h1
    have h2 : ((lam : ℂ) - hH.eigenvalues i) * inner ℂ (b i) z = 0 := by
      rw [sub_mul, h1, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (by exact_mod_cast (sub_eq_zero.mp h).symm) hi
    · exact h
  have hrep : ∀ z : EuclideanSpace ℂ ι, act A z = (lam : ℂ) • z →
      ∀ i0, hH.eigenvalues i0 = lam → z = inner ℂ (b i0) z • b i0 := by
    intro z hz i0 hi0
    conv_lhs => rw [← b.sum_repr' z]
    rw [Finset.sum_eq_single i0]
    · intro i _ hne
      rw [hcoef z hz i (fun h => hne (hev i i0 h hi0)), zero_smul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  obtain ⟨i0, hi0⟩ : ∃ i0, hH.eigenvalues i0 = lam := by
    by_contra hno
    push Not at hno
    have hx0 : x = 0 := by
      rw [← b.sum_repr' x]
      exact Finset.sum_eq_zero fun i _ => by rw [hcoef x hAx i (hno i), zero_smul]
    simp [IsState, hx0] at hx
  obtain ⟨cx, hcx⟩ : ∃ c, c = inner ℂ (b i0) x := ⟨_, rfl⟩
  obtain ⟨cy, hcy⟩ : ∃ c, c = inner ℂ (b i0) y := ⟨_, rfl⟩
  have hxr : x = cx • b i0 := by rw [hcx]; exact hrep x hAx i0 hi0
  have hyr : y = cy • b i0 := by rw [hcy]; exact hrep y hAy i0 hi0
  have hbn : ‖b i0‖ = 1 := b.orthonormal.1 i0
  have hcxn : ‖cx‖ = 1 := by
    have := congrArg norm hxr
    rw [norm_smul, hbn, mul_one] at this
    rw [← this]; exact hx
  have hcyn : ‖cy‖ = 1 := by
    have := congrArg norm hyr
    rw [norm_smul, hbn, mul_one] at this
    rw [← this]; exact hy
  refine ⟨cy * (starRingEnd ℂ) cx, by rw [norm_mul, Complex.norm_conj, hcxn, hcyn, one_mul], ?_⟩
  rw [hxr, hyr, smul_smul, mul_assoc, Complex.conj_mul', hcxn]
  simp
