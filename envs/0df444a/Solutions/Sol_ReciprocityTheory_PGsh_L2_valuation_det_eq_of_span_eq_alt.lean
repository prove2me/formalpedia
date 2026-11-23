-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.valuation_det_eq_of_span_eq_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:58.672546+00:00
-- url     : https://prove2.me/submissions/1bc51fc5-9a7d-4d58-b817-c3a294cfd78f

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Theorems.Thm_ReciprocityTheory_PGsh_L2_det_map_algebraMap
import Theorems.Thm_ReciprocityTheory_PGsh_L2_eq_one_of_le_one_of_mul_eq_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix Finset
namespace ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
private lemma cols_mul_lemma {X : Type} [Fintype X] [DecidableEq X] {P Q : Matrix X X C}
    (h : Submodule.span R (Set.range fun j x => Q x j) ≤
      Submodule.span R (Set.range fun j x => P x j)) :
    ∃ A : Matrix X X R, Q = P * A.map (algebraMap R C) := by
  have hc : ∀ j, ∃ c : X → R, ∑ i, c i • (fun x => P x i) = fun x => Q x j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun R).1 (h (Submodule.subset_span ⟨j, rfl⟩))
  choose c hc using hc
  refine ⟨Matrix.of fun i j => c j i, ?_⟩
  ext x j
  have hx := congrFun (hc j) x
  simp only [Finset.sum_apply, Pi.smul_apply] at hx
  rw [Matrix.mul_apply, ← hx]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Algebra.smul_def, mul_comm]
end ReciprocityTheory.PGsh.L2
end
end

set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    {P Q : Matrix X X C} (hP : IsUnit P.det)
    (h : Submodule.span R (Set.range fun j x => P x j) =
      Submodule.span R (Set.range fun j x => Q x j)) :
    v Q.det = v P.det := by
  obtain ⟨A, hA⟩ := cols_mul_lemma (R := R) h.ge
  obtain ⟨B, hB⟩ := cols_mul_lemma (R := R) h.le
  have hdQ : Q.det = P.det * algebraMap R C A.det := by
    rw [hA, Matrix.det_mul, det_map_algebraMap]
  have hdP : P.det = Q.det * algebraMap R C B.det := by
    rw [hB, Matrix.det_mul, det_map_algebraMap]
  have hAB : algebraMap R C A.det * algebraMap R C B.det = 1 := by
    refine mul_left_cancel₀ hP.ne_zero ?_
    calc P.det * (algebraMap R C A.det * algebraMap R C B.det)
        = P.det * algebraMap R C A.det * algebraMap R C B.det := (mul_assoc _ _ _).symm
      _ = P.det := by rw [← hdQ, ← hdP]
      _ = P.det * 1 := (mul_one _).symm
  have hvA : v (algebraMap R C A.det) = 1 :=
    eq_one_of_le_one_of_mul_eq_one (hv.map_le_one _) (hv.map_le_one _)
      (by rw [← map_mul v, hAB, map_one])
  rw [hdQ, map_mul, hvA, mul_one]
end ReciprocityTheory.PGsh.L2
