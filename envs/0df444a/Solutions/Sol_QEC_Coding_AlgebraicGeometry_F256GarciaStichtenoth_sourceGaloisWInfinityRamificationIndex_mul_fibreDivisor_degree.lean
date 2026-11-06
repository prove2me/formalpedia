-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWInfinityRamificationIndex_mul_fibreDivisor_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:15:36.016198+00:00
-- url     : https://prove2.me/submissions/c1a76a0f-156a-4525-a464-643c509402f0

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWResidueDegrees
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_FinitePlaceDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWFibreDivisors
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityFibreDivisor_degree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinity_fundamental_identity_relativeDegree


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
noncomputable section
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFibreDivisors_closurePolynomialAlgebra
attribute [local instance] sourceGaloisWFibreDivisors_closurePolynomialAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFibreDivisors_closurePolynomialRatFuncScalarTower
attribute [local instance] sourceGaloisWFibreDivisors_closurePolynomialRatFuncScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFibreDivisors_closureRatFuncIsSeparable
attribute [local instance] sourceGaloisWFibreDivisors_closureRatFuncIsSeparable
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFibreDivisors_sourceGaloisWZeroPrimeFintype
attribute [local instance] sourceGaloisWFibreDivisors_sourceGaloisWZeroPrimeFintype
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFibreDivisors_sourceGaloisWInfinityPrimeFintype
attribute [local instance] sourceGaloisWFibreDivisors_sourceGaloisWInfinityPrimeFintype
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFibreDivisors_sourceGaloisWZeroPrimeNonempty
attribute [local instance] sourceGaloisWFibreDivisors_sourceGaloisWZeroPrimeNonempty
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFibreDivisors_sourceGaloisWInfinityPrimeNonempty
attribute [local instance] sourceGaloisWFibreDivisors_sourceGaloisWInfinityPrimeNonempty
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    (sourceGaloisWInfinityRamificationIndex m : ℤ) *
        Divisor.degree GlobalPlace.residueDegree
          (sourceGaloisWInfinityFibreDivisor m) =
      (sourceGaloisWRelativeDegree m : ℤ) := by
  rw [sourceGaloisWInfinityFibreDivisor_degree]
  have h := congrArg (fun n : ℕ => (n : ℤ))
    (sourceGaloisWInfinity_fundamental_identity_relativeDegree m)
  norm_num only [Nat.cast_mul] at h
  calc
    (sourceGaloisWInfinityRamificationIndex m : ℤ) *
          ((Set.ncard (SourceGaloisWInfinityPrime m) : ℤ) *
            (sourceGaloisWInfinityInertiaDegree m : ℤ)) =
        (Set.ncard (SourceGaloisWInfinityPrime m) : ℤ) *
          ((sourceGaloisWInfinityRamificationIndex m : ℤ) *
            (sourceGaloisWInfinityInertiaDegree m : ℤ)) := by ring
    _ = (sourceGaloisWRelativeDegree m : ℤ) := h
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
