-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P13.contraction_preservesTetrahedron
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T23:44:25.424909+00:00
-- url     : https://prove2.me/submissions/d1c77365-b7c4-4e48-bdc1-b7e82d8f4005

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P13
open QAlgorithms.Papers.Independent.Intakethird100.P13
open scoped BigOperators


noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder



attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1706.05384v2 PDF pp.12--13, Lemma 22; the erroneous C2 weight table
is not used as a premise. -/
theorem solution (alpha : ℝ) (h0 : 0 ≤ alpha) (h1 : alpha ≤ 1)
    (q : BlochCoordinates) (hq : q ∈ pauliTetrahedron) :
    contractPoint alpha q ∈ pauliTetrahedron := by
  classical
  have hsqrt : (Real.sqrt alpha) ^ 2 = alpha := Real.sq_sqrt h0
  have hv (k : Fin 4) : contractPoint alpha (bellVertex k) ∈ pauliTetrahedron := by
    let r := contractPoint alpha (bellVertex k)
    let w : Fin 4 → ℝ := ![(1 + r 0 - r 1 + r 2) / 4,
      (1 + r 0 + r 1 - r 2) / 4, (1 - r 0 - r 1 - r 2) / 4,
      (1 - r 0 + r 1 + r 2) / 4]
    apply mem_convexHull_of_exists_fintype w bellVertex
    · intro j
      fin_cases k <;> fin_cases j <;>
        norm_num [w, r, contractPoint, bellVertex, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val'] <;>
        nlinarith [sq_nonneg (1 - Real.sqrt alpha), sq_nonneg (1 + Real.sqrt alpha)]
    · rw [Fin.sum_univ_four]
      change (1 + r 0 - r 1 + r 2) / 4 + (1 + r 0 + r 1 - r 2) / 4 +
        (1 - r 0 - r 1 - r 2) / 4 + (1 - r 0 + r 1 + r 2) / 4 = 1
      ring
    · intro i
      exact ⟨i, rfl⟩
    · ext i
      fin_cases i <;>
        simp [w, r, bellVertex, Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul] <;> ring
  let L : BlochCoordinates →ₗ[ℝ] BlochCoordinates :=
    { toFun := contractPoint alpha
      map_add' := by
        intro x y
        ext i
        fin_cases i <;> simp [contractPoint, mul_add]
      map_smul' := by
        intro a x
        ext i
        fin_cases i <;> simp [contractPoint, mul_left_comm, mul_assoc] }
  change L q ∈ pauliTetrahedron
  exact (convexHull_min (s := Set.range bellVertex) (t := L ⁻¹' pauliTetrahedron)
    (by rintro _ ⟨k, rfl⟩; exact hv k)
    ((convex_convexHull ℝ (Set.range bellVertex)).affine_preimage L.toAffineMap)) hq
