-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P15.erasure_syndrome_commutation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T01:12:24.838138+00:00
-- url     : https://prove2.me/submissions/c03c9f1f-66da-497f-8294-45b7a51cf36e

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P15

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P15 in
theorem solution (d n : ℕ) (hd : 2 ≤ d)
    (active : Fin n → Bool) (s : Finset (Fin n)) (U : (Matrix.specialUnitaryGroup (Fin d) ℂ)) :
    let P := erasurePatternProjector d n s
    let G := flaggedTransversal active (U : Matrix (Fin d) (Fin d) ℂ)
    P * G = G * P ∧
      ∀ rho : Matrix (FlaggedRegister d n) (FlaggedRegister d n) ℂ,
        IsDensityMatrix rho → P * rho * P = rho →
          conjSuperop P rho = rho ∧
          conjSuperop P (conjSuperop G rho) = conjSuperop G rho := by
  intro P G
  have hG0 : ∀ (x y : FlaggedRegister d n) (j : Fin n), ¬ (x j = none ↔ y j = none) →
      G x y = 0 := by
    intro x y j hj
    simp only [G, flaggedTransversal]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    revert hj
    generalize x j = a
    generalize y j = b
    intro hab
    cases a <;> cases b <;> simp_all [flaggedGate]
  have hPH : Pᴴ = P := by
    simp only [P, erasurePatternProjector, Matrix.diagonal_conjTranspose]
    congr 1
    funext x
    rw [Pi.star_apply]
    split_ifs <;> simp
  have hcomm : P * G = G * P := by
    ext x y
    simp only [P, erasurePatternProjector, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hx : ∀ j, (x j = none ↔ j ∈ s) <;> by_cases hy : ∀ j, (y j = none ↔ j ∈ s)
    · rw [if_pos hx, if_pos hy]; ring
    · obtain ⟨j, hj⟩ := not_forall.mp hy
      have h0 : G x y = 0 := hG0 x y j (fun h => hj (h.symm.trans (hx j)))
      rw [h0]; ring
    · obtain ⟨j, hj⟩ := not_forall.mp hx
      have h0 : G x y = 0 := hG0 x y j (fun h => hj (h.trans (hy j)))
      rw [h0]; ring
    · rw [if_neg hx, if_neg hy]; ring
  refine ⟨hcomm, ?_⟩
  intro rho _ hrho
  have hGP : Gᴴ * P = P * Gᴴ := by
    have h := congrArg Matrix.conjTranspose hcomm
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPH] at h
    exact h
  simp only [QAlgorithms.conjSuperop]
  rw [hPH]
  refine ⟨hrho, ?_⟩
  calc P * (G * rho * Gᴴ) * P = (P * G) * rho * (Gᴴ * P) := by
        simp only [Matrix.mul_assoc]
    _ = (G * P) * rho * (P * Gᴴ) := by rw [hcomm, hGP]
    _ = G * (P * rho * P) * Gᴴ := by simp only [Matrix.mul_assoc]
    _ = G * rho * Gᴴ := by rw [hrho]

end
