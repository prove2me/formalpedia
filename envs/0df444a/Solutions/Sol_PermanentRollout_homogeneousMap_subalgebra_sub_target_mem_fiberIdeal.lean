-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_subalgebra_sub_target_mem_fiberIdeal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/222c762e-7318-4f56-a783-403a388cb513

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} [Finite ι]
    (F : ι → MvPolynomial ι ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : ι → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0)
    (target : ι → ℂ)
    (t : homogeneousMapSubalgebra F) :
    (t : MvPolynomial ι ℂ) -
        MvPolynomial.C
          (((MvPolynomial.aeval target).comp
            (homogeneousMapCoordinateAlgEquiv F e he hF hzero).symm.toAlgHom) t) ∈
      homogeneousMapFiberIdeal F target := by
  classical
  let T := homogeneousMapSubalgebra F
  let I := homogeneousMapFiberIdeal F target
  let E := homogeneousMapCoordinateAlgEquiv F e he hF hzero
  let φ : T →ₐ[ℂ] ℂ := (MvPolynomial.aeval target).comp E.symm
  change (t : MvPolynomial ι ℂ) - MvPolynomial.C (φ t) ∈ I
  obtain ⟨x, hx⟩ := t
  change x - MvPolynomial.C (φ ⟨x, hx⟩) ∈ I
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have hcoordinate :
          E (MvPolynomial.X i) =
            ⟨F i, homogeneousMap_coordinate_mem_subalgebra F i⟩ := by
        apply Subtype.ext
        change MvPolynomial.bind₁ F (MvPolynomial.X i) = F i
        simp
      have hφ : φ ⟨F i, homogeneousMap_coordinate_mem_subalgebra F i⟩ =
          target i := by
        change MvPolynomial.aeval target
          (E.symm ⟨F i, homogeneousMap_coordinate_mem_subalgebra F i⟩) = _
        rw [← hcoordinate, E.symm_apply_apply]
        simp
      rw [hφ]
      change F i - MvPolynomial.C (target i) ∈
        Ideal.span (Set.range fun j => F j - MvPolynomial.C (target j))
      exact Ideal.subset_span (Set.mem_range_self i)
  | algebraMap c =>
      change MvPolynomial.C c -
        MvPolynomial.C (φ (algebraMap ℂ T c)) ∈ I
      simp
  | add x y hx hy ihx ihy =>
      change x + y -
        MvPolynomial.C (φ (⟨x, hx⟩ + ⟨y, hy⟩)) ∈ I
      rw [map_add, map_add]
      convert I.add_mem ihx ihy using 1
      ring
  | mul x y hx hy ihx ihy =>
      change x * y -
        MvPolynomial.C (φ (⟨x, hx⟩ * ⟨y, hy⟩)) ∈ I
      rw [map_mul, map_mul]
      have hmem := I.add_mem (I.mul_mem_right y ihx)
        (I.mul_mem_left (MvPolynomial.C (φ ⟨x, hx⟩)) ihy)
      convert hmem using 1
      ring
end PermanentRollout
