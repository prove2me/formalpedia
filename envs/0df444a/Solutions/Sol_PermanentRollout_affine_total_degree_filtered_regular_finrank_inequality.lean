-- Prove2me | solution 1 for PermanentRollout.affine_total_degree_filtered_regular_finrank_inequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/47ff3c63-d02f-4fbf-a53e-2bfba49abe8d

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_affine_total_degree_filtered_factor_surjective
import Theorems.Thm_PermanentRollout_affine_total_degree_filtered_mul_injective
import Theorems.Thm_PermanentRollout_affine_total_degree_filtered_mul_range_le_factor_ker

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} [Finite ι]
    (I : Ideal (MvPolynomial ι ℂ)) (g : MvPolynomial ι ℂ)
    (hregular : IsSMulRegular (MvPolynomial ι ℂ ⧸ I) g)
    (n : ℕ) :
    Module.finrank ℂ
        (affineTotalDegreeFilteredPiece
          (I ⊔ Ideal.span ({g} : Set (MvPolynomial ι ℂ)))
          (g.totalDegree + n)) +
      Module.finrank ℂ (affineTotalDegreeFilteredPiece I n) ≤
        Module.finrank ℂ
          (affineTotalDegreeFilteredPiece I (g.totalDegree + n)) := by
  let q := affineTotalDegreeFilteredFactor
    (show I ≤ I ⊔ Ideal.span ({g} : Set (MvPolynomial ι ℂ)) from
      le_sup_left)
    (g.totalDegree + n)
  let μ := affineTotalDegreeFilteredMul I g n
  have hμ : Function.Injective μ :=
    affine_total_degree_filtered_mul_injective I g hregular n
  have hq : Function.Surjective q :=
    affine_total_degree_filtered_factor_surjective
      (show I ≤ I ⊔ Ideal.span ({g} : Set (MvPolynomial ι ℂ)) from
        le_sup_left)
      (g.totalDegree + n)
  have hkernel : μ.range ≤ q.ker :=
    affine_total_degree_filtered_mul_range_le_factor_ker I g n
  have hμrank :
      Module.finrank ℂ μ.range =
        Module.finrank ℂ (affineTotalDegreeFilteredPiece I n) :=
    LinearMap.finrank_range_of_inj hμ
  have hqrank :
      Module.finrank ℂ q.range =
        Module.finrank ℂ
          (affineTotalDegreeFilteredPiece
            (I ⊔ Ideal.span ({g} : Set (MvPolynomial ι ℂ)))
              (g.totalDegree + n)) := by
    rw [LinearMap.range_eq_top_of_surjective q hq, finrank_top]
  have hkerle := Submodule.finrank_mono hkernel
  have hnullity := q.finrank_range_add_finrank_ker
  omega
end PermanentRollout
