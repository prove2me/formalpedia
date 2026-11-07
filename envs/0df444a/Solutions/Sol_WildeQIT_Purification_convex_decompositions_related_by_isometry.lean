-- Prove2me | solution 1 for WildeQIT.Purification.convex_decompositions_related_by_isometry
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T19:24:44.904411+00:00
-- url     : https://prove2.me/submissions/a596acda-3600-4781-a165-9140f3e17876

import Mathlib
import Definitions.Def_HarlowTASI_QuantumBasics
import Theorems.Thm_WildeQIT_Purification_exists_unitary_eq_mul_of_mul_conjTranspose_eq

open Matrix WildeQIT.Purification

theorem solution {a : Type} [Fintype a] {d d' : ℕ}
    (hd : d' ≤ d) (ρ : Matrix a a ℂ)
    (pX : Fin d → ℝ) (pY : Fin d' → ℝ) (ψ : Fin d → a → ℂ) (φ : Fin d' → a → ℂ)
    (hpX_nonneg : ∀ x, 0 ≤ pX x) (hpX_sum : ∑ x, pX x = 1)
    (hpY_nonneg : ∀ y, 0 ≤ pY y) (hpY_sum : ∑ y, pY y = 1)
    (hψ : ∀ x, ∑ i, Complex.normSq (ψ x i) = 1) (hφ : ∀ y, ∑ i, Complex.normSq (φ y i) = 1)
    (hρX : ρ = ∑ x, (pX x : ℂ) • Matrix.vecMulVec (ψ x) (star (ψ x)))
    (hρY : ρ = ∑ y, (pY y : ℂ) • Matrix.vecMulVec (φ y) (star (φ y))) :
    ∃ U : Matrix (Fin d) (Fin d') ℂ, HarlowTASI.IsIsometry U ∧
      ∀ x, (Real.sqrt (pX x) : ℂ) • ψ x = ∑ y, (U x y * (Real.sqrt (pY y) : ℂ)) • φ y := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
  have hsq : ∀ r : ℝ, 0 ≤ r → (Real.sqrt r : ℂ) * star (Real.sqrt r : ℂ) = (r : ℂ) := by
    intro r hr
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hr]
  let A : Matrix a (Fin (d' + k)) ℂ := Matrix.of fun i x => (Real.sqrt (pX x) : ℂ) * ψ x i
  let B : Matrix a (Fin (d' + k)) ℂ :=
    Matrix.of fun i => Fin.append (fun y => (Real.sqrt (pY y) : ℂ) * φ y i) (fun _ => 0)
  have hA : A * Aᴴ = ρ := by
    rw [hρX]
    ext i j
    simp only [A, Matrix.mul_apply, conjTranspose_apply, of_apply, Matrix.sum_apply,
      Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul, star_mul']
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← hsq _ (hpX_nonneg x)]
    ring
  have hB : B * Bᴴ = ρ := by
    rw [hρY]
    ext i j
    simp only [B, Matrix.mul_apply, conjTranspose_apply, of_apply, Matrix.sum_apply,
      Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul, Fin.sum_univ_add,
      Fin.append_left, Fin.append_right, star_zero, mul_zero, Finset.sum_const_zero, add_zero,
      star_mul']
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← hsq _ (hpY_nonneg y)]
    ring
  obtain ⟨U, hU, hAB⟩ := exists_unitary_eq_mul_of_mul_conjTranspose_eq A B (hA.trans hB.symm)
  have hUU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  refine ⟨Matrix.of fun x y => U (Fin.castAdd k y) x, ?_, fun x => ?_⟩
  · unfold HarlowTASI.IsIsometry
    ext y y'
    have := congrFun (congrFun hUU (Fin.castAdd k y')) (Fin.castAdd k y)
    simp only [Matrix.mul_apply, star_apply, conjTranspose_apply, of_apply,
      Matrix.one_apply, (Fin.castAdd_injective d' k).eq_iff] at this ⊢
    rw [show (if y = y' then (1 : ℂ) else 0) = if y' = y then 1 else 0 by
      by_cases hyy : y = y'
      · simp [hyy]
      · simp [hyy, Ne.symm hyy], ← this]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  · funext i
    have := congrFun (congrFun hAB i) x
    simp only [A, B, Matrix.mul_apply, of_apply, Fin.sum_univ_add, Fin.append_left,
      Fin.append_right, zero_mul, Finset.sum_const_zero, add_zero] at this
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [of_apply]
    ring
