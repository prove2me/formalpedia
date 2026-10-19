-- Prove2me | solution 1 for PermanentRollout.homogeneousMapFiber_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/ef175256-215f-40ca-9967-709805e8afae

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_subalgebra_sub_target_mem_fiberIdeal

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
    (target : ι → ℂ) :
    FiniteDimensional ℂ
      (MvPolynomial ι ℂ ⧸ homogeneousMapFiberIdeal F target) := by
  classical
  let T := homogeneousMapSubalgebra F
  let S := MvPolynomial ι ℂ
  let I := homogeneousMapFiberIdeal F target
  let E := homogeneousMapCoordinateAlgEquiv F e he hF hzero
  let φ : T →ₐ[ℂ] ℂ := (MvPolynomial.aeval target).comp E.symm
  letI : RingHomSurjective φ.toRingHom :=
    ⟨by
      intro c
      refine ⟨algebraMap ℂ T c, ?_⟩
      exact φ.commutes c⟩
  letI : Module.Finite T S := homogeneousMap_moduleFinite F e he hF hzero
  let π : S →ₛₗ[φ.toRingHom] (S ⧸ I) :=
    { toFun := Ideal.Quotient.mk I
      map_add' := (Ideal.Quotient.mk I).map_add
      map_smul' := by
        intro t s
        change Ideal.Quotient.mk I ((t : S) * s) =
          φ t • (Ideal.Quotient.mkₐ ℂ I) s
        calc
          Ideal.Quotient.mk I ((t : S) * s) =
              Ideal.Quotient.mk I (MvPolynomial.C (φ t) * s) := by
            apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
            rw [← sub_mul]
            apply I.mul_mem_right s
            exact homogeneousMap_subalgebra_sub_target_mem_fiberIdeal
              F e he hF hzero target t
          _ = φ t • (Ideal.Quotient.mkₐ ℂ I) s := by
            calc
              Ideal.Quotient.mk I (MvPolynomial.C (φ t) * s) =
                  (Ideal.Quotient.mkₐ ℂ I) (φ t • s) := by
                change Ideal.Quotient.mk I (MvPolynomial.C (φ t) * s) =
                  Ideal.Quotient.mk I (φ t • s)
                apply congrArg (Ideal.Quotient.mk I)
                exact (Algebra.smul_def (φ t) s).symm
              _ = φ t • (Ideal.Quotient.mkₐ ℂ I) s :=
                (Ideal.Quotient.mkₐ ℂ I).toLinearMap.map_smul (φ t) s }
  exact Module.Finite.of_surjective π Ideal.Quotient.mk_surjective
end PermanentRollout
