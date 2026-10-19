-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allTarget_rees_isScalarTower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/535a3f94-f75a-4141-b979-1c8944c23e10

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMapReesTargetHom_coordinate
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_rees_source_coordinate

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
open scoped BigOperators
open scoped Pointwise
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ) (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0) :
    @IsScalarTower
      (homogeneousMapSubalgebra F)
      (Polynomial ℂ)
      (homogeneousMapAllTargetReesQuotient F target e)
      (@Algebra.toSMul
        (homogeneousMapSubalgebra F) (Polynomial ℂ)
        inferInstance inferInstance
        (homogeneousMapReesTargetHom
          F e he hF hzero target).toRingHom.toAlgebra)
      (@Algebra.toSMul
        (Polynomial ℂ) (homogeneousMapAllTargetReesQuotient F target e)
        inferInstance inferInstance
        (homogeneousMapAllTargetReesParameterAlgebra F target e))
      (@Algebra.toSMul
        (homogeneousMapSubalgebra F)
        (homogeneousMapAllTargetReesQuotient F target e)
        inferInstance inferInstance
        (homogeneousMapAllTargetReesSourceAlgebra F target e)) := by
  letI : Algebra (homogeneousMapSubalgebra F) (Polynomial ℂ) :=
    (homogeneousMapReesTargetHom
      F e he hF hzero target).toRingHom.toAlgebra
  letI : Algebra (Polynomial ℂ)
      (homogeneousMapAllTargetReesQuotient F target e) :=
    homogeneousMapAllTargetReesParameterAlgebra F target e
  letI : Algebra (homogeneousMapSubalgebra F)
      (homogeneousMapAllTargetReesQuotient F target e) :=
    homogeneousMapAllTargetReesSourceAlgebra F target e
  apply IsScalarTower.of_algebraMap_eq
  intro x
  let E := homogeneousMapCoordinateAlgEquiv F e he hF hzero
  obtain ⟨p, rfl⟩ := E.surjective x
  induction p using MvPolynomial.induction_on with
  | C c =>
      have hEc : (E (MvPolynomial.C c) : MvPolynomial (Fin k) ℂ) =
          MvPolynomial.C c := by
        simpa using congrArg
          (fun z : homogeneousMapSubalgebra F =>
            (z : MvPolynomial (Fin k) ℂ)) (E.commutes c)
      simp [RingHom.algebraMap_toAlgebra,
        homogeneousMapAllTargetReesSourceRingHom,
        homogeneousMapAllTargetReesParameterRingHom,
        homogeneousMapReesTargetHom, E, hEc]
  | add p q hp hq =>
      simpa [map_add] using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
      have hE : E (MvPolynomial.X i) =
          (⟨F i, homogeneousMap_coordinate_mem_subalgebra F i⟩ :
            homogeneousMapSubalgebra F) := by
        apply Subtype.ext
        change MvPolynomial.aeval F (MvPolynomial.X i) = F i
        simp
      rw [map_mul, map_mul, map_mul]
      rw [hp, hE]
      rw [map_mul]
      change _ *
          homogeneousMapAllTargetReesSourceRingHom F target e
            (⟨F i, homogeneousMap_coordinate_mem_subalgebra F i⟩ :
              homogeneousMapSubalgebra F) =
        _ * homogeneousMapAllTargetReesParameterRingHom F target e
          (homogeneousMapReesTargetHom
            F e he hF hzero target
            (⟨F i, homogeneousMap_coordinate_mem_subalgebra F i⟩ :
              homogeneousMapSubalgebra F))
      rw [homogeneousMapReesTargetHom_coordinate]
      rw [homogeneousMap_allTarget_rees_source_coordinate]
end PermanentRollout
