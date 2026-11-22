-- Prove2me | solution 1 for ShiShallow.exists_width_cast_reindexing_isometry
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-16T01:13:59.194281+00:00
-- url     : https://prove2.me/submissions/d26b005c-8c05-4efa-a75b-a99441668c7a

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Width-cast reindexing isometry.  For `h : K = M` the relabelling `z ↦ z ∘ Fin.cast h.symm`
is a bijection `Bits K → Bits M`; its explicit 0/1 placement matrix `R` is an isometry,
acts as that relabelling on states, and preserves `∑ ‖·‖^2` (hence `Normalized`).
No `Nonempty`/`Classical.choice` is used: the matrix is written down.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

open ShiShallow

/-- Reindex a `K`-bit string as an `M`-bit string along `h : K = M`. -/
private def shiPi_reix {K M : ℕ} (h : K = M) (z : Bits K) : Bits M :=
  fun i : Fin M => z (Fin.cast h.symm i)

/-- The inverse relabelling. -/
private def shiPi_unreix {K M : ℕ} (h : K = M) (y : Bits M) : Bits K :=
  fun j : Fin K => y (Fin.cast h j)

private lemma shiPi_cast_left {K M : ℕ} (h : K = M) (j : Fin K) :
    Fin.cast h.symm (Fin.cast h j) = j :=
  Fin.ext rfl

private lemma shiPi_cast_right {K M : ℕ} (h : K = M) (i : Fin M) :
    Fin.cast h (Fin.cast h.symm i) = i :=
  Fin.ext rfl

private lemma shiPi_left_inv {K M : ℕ} (h : K = M) (z : Bits K) :
    shiPi_unreix h (shiPi_reix h z) = z := by
  funext j
  exact congrArg z (shiPi_cast_left h j)

private lemma shiPi_right_inv {K M : ℕ} (h : K = M) (y : Bits M) :
    shiPi_reix h (shiPi_unreix h y) = y := by
  funext i
  exact congrArg y (shiPi_cast_right h i)

private lemma shiPi_reix_bijective {K M : ℕ} (h : K = M) :
    Function.Bijective (shiPi_reix h) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨shiPi_unreix h, shiPi_left_inv h, shiPi_right_inv h⟩

private lemma shiPi_unreix_inj {K M : ℕ} (h : K = M) {y y' : Bits M}
    (hy : shiPi_unreix h y = shiPi_unreix h y') : y = y' :=
  ((shiPi_right_inv h y).symm.trans (congrArg (shiPi_reix h) hy)).trans
    (shiPi_right_inv h y')

/-- The placement condition, read from either side. -/
private lemma shiPi_eq_iff {K M : ℕ} (h : K = M) (z : Bits K) (y : Bits M) :
    y = shiPi_reix h z ↔ z = shiPi_unreix h y := by
  constructor
  · intro hy
    subst hy
    exact (shiPi_left_inv h z).symm
  · intro hz
    subst hz
    exact (shiPi_right_inv h y).symm

/-- The explicit 0/1 reindexing matrix. -/
private def shiPi_mat {K M : ℕ} (h : K = M) : Matrix (Bits K) (Bits M) ℂ :=
  Matrix.of fun z y => if y = shiPi_reix h z then 1 else 0

private lemma shiPi_mat_apply {K M : ℕ} (h : K = M) (z : Bits K) (y : Bits M) :
    shiPi_mat h z y = if y = shiPi_reix h z then 1 else 0 := rfl

private lemma shiPi_mat_apply' {K M : ℕ} (h : K = M) (z : Bits K) (y : Bits M) :
    shiPi_mat h z y = if z = shiPi_unreix h y then 1 else 0 := by
  by_cases hq : z = shiPi_unreix h y
  · have hp : y = shiPi_reix h z := (shiPi_eq_iff h z y).mpr hq
    rw [shiPi_mat_apply, if_pos hp, if_pos hq]
  · have hp : ¬ (y = shiPi_reix h z) := fun hh => hq ((shiPi_eq_iff h z y).mp hh)
    rw [shiPi_mat_apply, if_neg hp, if_neg hq]

/-- The reindexing matrix is an isometry. -/
private lemma shiPi_mat_iso {K M : ℕ} (h : K = M) :
    Matrix.conjTranspose (shiPi_mat h) * shiPi_mat h = (1 : Op M) := by
  refine Matrix.ext fun y y' => ?_
  rw [Matrix.mul_apply]
  by_cases hyy : y = y'
  · rw [← hyy]
    have h1 : ∀ z : Bits K,
        Matrix.conjTranspose (shiPi_mat h) y z * shiPi_mat h z y
          = if z = shiPi_unreix h y then (1 : ℂ) else 0 := by
      intro z
      rw [Matrix.conjTranspose_apply, shiPi_mat_apply' h z y]
      by_cases hz : z = shiPi_unreix h y
      · rw [if_pos hz, star_one, one_mul]
      · rw [if_neg hz, star_zero, zero_mul]
    rw [Matrix.one_apply_eq]
    simp only [h1]
    exact Fintype.sum_ite_eq' (shiPi_unreix h y) (fun _ => (1 : ℂ))
  · rw [Matrix.one_apply_ne hyy]
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [Matrix.conjTranspose_apply, shiPi_mat_apply' h z y, shiPi_mat_apply' h z y']
    by_cases hz : z = shiPi_unreix h y
    · have hne : ¬ (z = shiPi_unreix h y') := fun hh =>
        hyy (shiPi_unreix_inj h (hz.symm.trans hh))
      rw [if_pos hz, if_neg hne, star_one, one_mul]
    · rw [if_neg hz, star_zero, zero_mul]

/-- The action law: the matrix relabels the argument of the state. -/
private lemma shiPi_mat_mulVec {K M : ℕ} (h : K = M) (Psi : QState M) :
    Matrix.mulVec (shiPi_mat h) Psi
      = fun z : Bits K => Psi (fun i : Fin M => z (Fin.cast h.symm i)) := by
  funext z
  rw [Matrix.mulVec_apply_eq_sum]
  have hs : ∀ y : Bits M,
      shiPi_mat h z y * Psi y = if y = shiPi_reix h z then Psi y else 0 := by
    intro y
    by_cases hy : y = shiPi_reix h z
    · rw [shiPi_mat_apply, if_pos hy, if_pos hy, one_mul]
    · rw [shiPi_mat_apply, if_neg hy, if_neg hy, zero_mul]
  simp only [hs]
  exact Fintype.sum_ite_eq' (shiPi_reix h z) Psi

/-- Total probability is preserved: this is what transports `Normalized`. -/
private lemma shiPi_mat_norm {K M : ℕ} (h : K = M) (Psi : QState M) :
    (∑ z : Bits K, ‖Matrix.mulVec (shiPi_mat h) Psi z‖ ^ 2)
      = ∑ y : Bits M, ‖Psi y‖ ^ 2 := by
  simp only [shiPi_mat_mulVec h Psi]
  exact Fintype.sum_bijective (shiPi_reix h) (shiPi_reix_bijective h)
    (fun z : Bits K => ‖Psi (shiPi_reix h z)‖ ^ 2)
    (fun y : Bits M => ‖Psi y‖ ^ 2) (fun _ => rfl)

/-- A width cast `K = M` is implemented by an explicit reindexing isometry, which acts by
relabelling the basis string and preserves the total squared norm. -/
theorem solution {K M : ℕ} (h : K = M) :
    ∃ R : Matrix (ShiShallow.Bits K) (ShiShallow.Bits M) ℂ,
      Matrix.conjTranspose R * R = (1 : ShiShallow.Op M) ∧
      (∀ Ψ : ShiShallow.QState M,
          Matrix.mulVec R Ψ
            = fun z : ShiShallow.Bits K => Ψ (fun i : Fin M => z (Fin.cast h.symm i))) ∧
      (∀ Ψ : ShiShallow.QState M,
          (∑ z : ShiShallow.Bits K, ‖Matrix.mulVec R Ψ z‖ ^ 2)
            = ∑ y : ShiShallow.Bits M, ‖Ψ y‖ ^ 2) :=
  ⟨shiPi_mat h, shiPi_mat_iso h, fun Ψ => shiPi_mat_mulVec h Ψ,
    fun Ψ => shiPi_mat_norm h Ψ⟩
