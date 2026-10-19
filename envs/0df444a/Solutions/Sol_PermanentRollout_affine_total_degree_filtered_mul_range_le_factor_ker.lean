-- Prove2me | solution 1 for PermanentRollout.affine_total_degree_filtered_mul_range_le_factor_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/70fcb447-5d2b-4b76-b4b9-efab72d80c54

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} (I : Ideal (MvPolynomial ι ℂ))
    (g : MvPolynomial ι ℂ) (n : ℕ) :
    (affineTotalDegreeFilteredMul I g n).range ≤
      (affineTotalDegreeFilteredFactor
        (show I ≤ I ⊔ Ideal.span ({g} : Set (MvPolynomial ι ℂ)) from
          le_sup_left)
        (g.totalDegree + n)).ker := by
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
  apply LinearMap.mem_ker.mpr
  apply Subtype.ext
  change
    Ideal.Quotient.factorₐ ℂ
        (show I ≤ I ⊔ Ideal.span ({g} : Set (MvPolynomial ι ℂ)) from
          le_sup_left)
      (Ideal.Quotient.mk I g *
        (y : MvPolynomial ι ℂ ⧸ I)) = 0
  rw [map_mul]
  have hg :
      Ideal.Quotient.mk (I ⊔ Ideal.span ({g} : Set (MvPolynomial ι ℂ))) g =
        0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact
      (show Ideal.span ({g} : Set (MvPolynomial ι ℂ)) ≤
        I ⊔ Ideal.span ({g} : Set (MvPolynomial ι ℂ)) from le_sup_right)
        (Ideal.subset_span (by simp))
  change
    Ideal.Quotient.mk (I ⊔ Ideal.span ({g} : Set (MvPolynomial ι ℂ))) g *
      _ = 0
  rw [hg, zero_mul]
end PermanentRollout
