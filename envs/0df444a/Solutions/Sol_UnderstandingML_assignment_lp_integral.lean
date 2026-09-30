-- Prove2me | solution 1 for UnderstandingML.assignment_lp_integral
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T06:40:54.56543+00:00
-- url     : https://prove2.me/submissions/64b77f2c-5151-48e7-ae22-2ba9f074f411

import Definitions.Def_UnderstandingML_Multiclass

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

theorem solution {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) :
    ∃ σ : Equiv.Perm (Fin r), ∀ B ∈ doublyStochastic ℝ (Fin r),
      matrixInner A (σ.permMatrix ℝ) ≤ matrixInner A B := by
  obtain ⟨σ, -, hσ⟩ := Finset.exists_min_image (Finset.univ : Finset (Equiv.Perm (Fin r)))
    (fun σ ↦ matrixInner A (σ.permMatrix ℝ)) Finset.univ_nonempty
  refine ⟨σ, fun B hB ↦ ?_⟩
  have hB' : B ∈ convexHull ℝ {x | ∃ τ : Equiv.Perm (Fin r), τ.permMatrix ℝ = x} := by
    rw [← doublyStochastic_eq_convexHull_permMatrix]; exact hB
  have hlin : ConcaveOn ℝ Set.univ (fun B : Matrix (Fin r) (Fin r) ℝ ↦ matrixInner A B) := by
    let L : Matrix (Fin r) (Fin r) ℝ →ₗ[ℝ] ℝ :=
      { toFun := fun B ↦ matrixInner A B
        map_add' := fun B C ↦ by
          simp only [matrixInner, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
        map_smul' := fun c B ↦ by
          simp only [matrixInner, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
          ring }
    exact L.concaveOn convex_univ
  obtain ⟨M, ⟨τ, rfl⟩, hM⟩ := hlin.exists_le_of_mem_convexHull (Set.subset_univ _) hB'
  exact (hσ τ (Finset.mem_univ _)).trans hM
