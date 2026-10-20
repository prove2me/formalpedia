-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P17.generalizedPauli_unital
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:51:49.976822+00:00
-- url     : https://prove2.me/submissions/04d57d28-9f95-4270-bf6e-2505c9f565a3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17

noncomputable section
open scoped BigOperators Matrix ComplexConjugate ComplexOrder TensorProduct

open QAlgorithms.Papers.Independent.Dependency50.P49 (transposeMap)

open QAlgorithms.Papers.Independent.Frontier18.P17

lemma g52_phase (d : ℕ) [NeZero d] (x : ZMod d) :
    star (QAlgorithms.Papers.Independent.Information100.P34.cyclicPhase d x) *
      QAlgorithms.Papers.Independent.Information100.P34.cyclicPhase d x = 1 := by
  unfold QAlgorithms.Papers.Independent.Information100.P34.cyclicPhase
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  convert Complex.exp_zero
  rw [map_div₀, map_mul, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, map_natCast,
    map_natCast, map_ofNat]
  ring

lemma g52_weyl_unitary (d : ℕ) [NeZero d] (n m : ZMod d) :
    QAlgorithms.Papers.Independent.Information100.P34.weyl (d := d) n m ∈
      Matrix.unitaryGroup (ZMod d) ℂ := by
  unfold QAlgorithms.Papers.Independent.Information100.P34.weyl
  refine Submonoid.mul_mem _ (Submonoid.pow_mem _ ?_ _) (Submonoid.pow_mem _ ?_ _)
  · rw [Matrix.mem_unitaryGroup_iff']
    ext a c
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply]
    simp [apply_ite star]
    by_cases h : a = c
    · subst h; simp
    · simp [h, Ne.symm h]
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1; funext x
    exact g52_phase d x

lemma g52_f_bij (d : ℕ) [NeZero d] : Function.Bijective (fun i : Fin d => (i.val : ZMod d)) := by
  have hinj : Function.Injective (fun i : Fin d => (i.val : ZMod d)) := by
    intro i j h
    have := congrArg ZMod.val h
    simp only [ZMod.val_natCast_of_lt i.isLt, ZMod.val_natCast_of_lt j.isLt] at this
    exact Fin.ext this
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp [ZMod.card]⟩

lemma g52_sub_unitary (d : ℕ) [NeZero d] {U : Matrix (ZMod d) (ZMod d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (ZMod d) ℂ) :
    U.submatrix (fun i : Fin d => (i.val : ZMod d)) (fun i : Fin d => (i.val : ZMod d)) ∈
      Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hU ⊢
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul _ _ _ _ _
    (g52_f_bij d), ← Matrix.star_eq_conjTranspose, hU, Matrix.submatrix_one _ (g52_f_bij d).1]

theorem solution {d : ℕ} [NeZero d] (hd : 0 < d)
    (p : (Fin d × Fin d) → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) :
    (∀ a : Fin d × Fin d, ((QAlgorithms.Papers.Independent.Information100.P34.weyl
      (d := d) (-(a.1.val : ZMod d)) (a.2.val : ZMod d)).submatrix
        (fun i : Fin d => (i.val : ZMod d)) (fun i : Fin d => (i.val : ZMod d))) ∈ Matrix.unitaryGroup (Fin d) ℂ) ∧
    QAlgorithms.IsChannel (pauliChannel d p) ∧ pauliChannel d p 1 = 1 := by
  set W : Fin d × Fin d → Matrix (Fin d) (Fin d) ℂ := fun a =>
    (QAlgorithms.Papers.Independent.Information100.P34.weyl
      (d := d) (-(a.1.val : ZMod d)) (a.2.val : ZMod d)).submatrix
        (fun i : Fin d => (i.val : ZMod d)) (fun i : Fin d => (i.val : ZMod d)) with hW
  have hU : ∀ a, W a ∈ Matrix.unitaryGroup (Fin d) ℂ := fun a =>
    g52_sub_unitary d (g52_weyl_unitary d _ _)
  have hU1 : ∀ a, (W a)ᴴ * W a = 1 := fun a => by
    have := hU a; rw [Matrix.mem_unitaryGroup_iff'] at this; exact this
  have hU2 : ∀ a, W a * (W a)ᴴ = 1 := fun a => by
    have := hU a; rw [Matrix.mem_unitaryGroup_iff] at this; exact this
  have hsq : ∀ a, ((Real.sqrt (p a) : ℝ) : ℂ) * ((Real.sqrt (p a) : ℝ) : ℂ) = (p a : ℂ) := fun a => by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hp a)]
  have hsumC : ∑ a, (p a : ℂ) = 1 := by exact_mod_cast hsum
  have hpc : ∀ ρ, pauliChannel d p ρ = ∑ a, (p a : ℂ) • (W a * ρ * (W a)ᴴ) := fun ρ => rfl
  refine ⟨hU, ?_, ?_⟩
  · let e := Fintype.equivFin (Fin d × Fin d)
    refine ⟨Fintype.card (Fin d × Fin d), fun j => ((Real.sqrt (p (e.symm j)) : ℝ) : ℂ) • W (e.symm j),
      ?_, ?_⟩
    · unfold QAlgorithms.IsKrausFamily
      rw [Equiv.sum_comp e.symm (fun a => (((Real.sqrt (p a) : ℝ) : ℂ) • W a)ᴴ *
        (((Real.sqrt (p a) : ℝ) : ℂ) • W a))]
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hU1,
        Complex.star_def, Complex.conj_ofReal, hsq]
      rw [← Finset.sum_smul, hsumC, one_smul]
    · intro ρ
      unfold QAlgorithms.krausApply
      rw [Equiv.sum_comp e.symm (fun a => (((Real.sqrt (p a) : ℝ) : ℂ) • W a) * ρ *
        (((Real.sqrt (p a) : ℝ) : ℂ) • W a)ᴴ), hpc]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Complex.star_def, Complex.conj_ofReal, hsq]
  · rw [hpc]
    simp only [Matrix.mul_one, hU2]
    rw [← Finset.sum_smul, hsumC, one_smul]
