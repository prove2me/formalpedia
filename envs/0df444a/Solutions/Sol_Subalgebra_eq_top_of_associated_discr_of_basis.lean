-- Prove2me | solution 1 for Subalgebra.eq_top_of_associated_discr_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/a2390e1b-8559-5368-aadd-15597c30772a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subalgebra_eq_top_of_associated_discr_of_basis

set_option autoImplicit false

theorem solution
    {R A ι : Type} [CommRing R] [IsDomain R] [CommRing A] [Algebra R A] [Fintype ι] [DecidableEq ι]
    (b' : Module.Basis ι R A) (B : Subalgebra R A) (b : Module.Basis ι R ↥B)
    (hdiscr : Associated (Algebra.discr R (fun i => ((b i : ↥B) : A))) (Algebra.discr R b'))
    (hne : Algebra.discr R b' ≠ 0) : B = ⊤ := by
  classical
  let P : Matrix ι ι R := fun i j => b'.repr ((b i : ↥B) : A) j
  have hbP' : (fun i => ((b i : ↥B) : A)) = (P.map (algebraMap R A)).mulVec (b' : ι → A) := by
    funext i
    conv_lhs => rw [← b'.sum_repr ((b i : ↥B) : A)]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.smul_def, P]
  have hdisc : Algebra.discr R (fun i => ((b i : ↥B) : A)) = P.det ^ 2 * Algebra.discr R b' := by
    rw [hbP', Algebra.discr_of_matrix_mulVec]
  obtain ⟨u, hu⟩ := hdiscr

  have hunit : IsUnit P.det := by
    have h1 : (P.det ^ 2 * (u : R) - 1) * Algebra.discr R b' = 0 := by
      rw [sub_mul, one_mul, mul_right_comm, ← hdisc, hu, sub_self]
    have h2 : P.det ^ 2 * (u : R) = 1 := sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_right hne)
    rw [pow_two, mul_assoc] at h2
    exact IsUnit.of_mul_eq_one _ h2

  have hb' : ∀ j, b' j ∈ B := by
    intro j
    have hinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hunit
    have : (b' : ι → A) = ((P⁻¹).map (algebraMap R A)).mulVec (fun i => ((b i : ↥B) : A)) := by
      rw [hbP', Matrix.mulVec_mulVec, ← Matrix.map_mul, hinv,
        Matrix.map_one (algebraMap R A) (map_zero _) (map_one _), Matrix.one_mulVec]
    have hj := congrFun this j
    rw [hj]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine B.sum_mem fun i _ => ?_
    rw [← Algebra.smul_def]
    exact B.smul_mem (b i).2 _
  rw [eq_top_iff]
  intro a _
  rw [← b'.sum_repr a]
  exact B.sum_mem fun j _ => B.smul_mem (hb' j) _

end S_Subalgebra_eq_top_of_associated_discr_of_basis
end P2MW
export P2MW.S_Subalgebra_eq_top_of_associated_discr_of_basis (solution)
