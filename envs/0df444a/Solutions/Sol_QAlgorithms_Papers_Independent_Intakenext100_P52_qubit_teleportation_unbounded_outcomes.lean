-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P52.qubit_teleportation_unbounded_outcomes
-- status  : ACCEPTED   (prove)
-- author  : @Mceppaglia
-- created : 2026-11-20T13:41:05.623176+00:00
-- url     : https://prove2.me/submissions/59979f30-93d6-4ea8-8cd6-fecfd0ba98e7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Intakenext100.P52

/-- The first bit selects a flip, and the second selects a sign on the true row. -/
private def bellU (p : Bool × Bool) : Matrix Bool Bool ℂ :=
  fun a b => if b = Bool.xor a p.1 then (if p.2 && a then -1 else 1) else 0

private lemma bell_unitary (p : Bool × Bool) : bellU p ∈ Matrix.unitaryGroup Bool ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  ext a b
  obtain ⟨x, z⟩ := p
  cases x <;> cases z <;> cases a <;> cases b <;>
    simp [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, bellU]

/-- Coordinates of the rotated maximally entangled qubit pair. -/
private lemma bell_rotated_entry (U : Matrix Bool Bool ℂ) (x y : Bool) :
    rotatedEntangledKet U (x, y) = star (U y x) * ((Real.sqrt 2 : ℂ)⁻¹) := by
  simp [rotatedEntangledKet, act, finiteMaxEntangled, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.one_apply, mul_ite, ite_mul]

/-- The four rotated Bell projectors resolve the identity. -/
private lemma bell_sum :
    (∑ p : Bool × Bool, pureDensity (rotatedEntangledKet (bellU p))) = 1 := by
  have hs : ((Real.sqrt 2 : ℂ) ^ 2) = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [Matrix.sum_apply, Fintype.sum_prod_type, pureDensity,
      bell_rotated_entry, bellU] <;>
    field_simp [hs0] <;> linear_combination -hs

/-- Split each of the four primitive effects into equally weighted copies. -/
private theorem repeat_bell_frame
    (U₀ : Bool × Bool → Matrix Bool Bool ℂ)
    (hU : ∀ p, U₀ p ∈ Matrix.unitaryGroup Bool ℂ)
    (hframe : ∑ p, pureDensity (rotatedEntangledKet (U₀ p)) = 1) :
    ∀ N : ℕ, ∃ n : ℕ, N < n ∧ 4 < n ∧
      ∃ (U : Fin n → Matrix Bool Bool ℂ) (k : Fin n → ℝ),
        (∀ i, U i ∈ Matrix.unitaryGroup Bool ℂ) ∧ (∀ i, 0 < k i) ∧ BellFrame U k := by
  classical
  intro N
  let m := N + 2
  let e := Fintype.equivFin ((Bool × Bool) × Fin m)
  have hcard : Fintype.card ((Bool × Bool) × Fin m) = 4 * m := by
    simp
  refine ⟨_, by rw [hcard]; dsimp [m]; omega, by rw [hcard]; dsimp [m]; omega,
    (fun i => U₀ (e.symm i).1), (fun _ => (m : ℝ)⁻¹),
    (fun i => hU (e.symm i).1), (fun _ => by dsimp [m]; positivity), ?_⟩
  unfold BellFrame
  rw [← e.sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Complex.ofReal_inv, Complex.ofReal_natCast]
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (N + 1)
  simpa only [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hm, Fintype.sum_prod_type] using hframe

theorem solution :
    ∀ N : ℕ, ∃ n : ℕ, N < n ∧ 4 < n ∧
      ∃ (U : Fin n → Matrix Bool Bool ℂ) (k : Fin n → ℝ),
        (∀ i, U i ∈ Matrix.unitaryGroup Bool ℂ) ∧ (∀ i, 0 < k i) ∧ BellFrame U k :=
  repeat_bell_frame bellU bell_unitary bell_sum

end
