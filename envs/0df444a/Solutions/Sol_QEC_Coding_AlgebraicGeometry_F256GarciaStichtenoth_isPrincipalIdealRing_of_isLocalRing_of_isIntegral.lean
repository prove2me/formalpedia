-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.isPrincipalIdealRing_of_isLocalRing_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:33:48.802581+00:00
-- url     : https://prove2.me/submissions/9a4cfd9c-9eb5-4570-a583-16ad7a26b644

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.PID
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalIntegralClosureFree

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (A B : Type*)
    [CommRing A] [CommRing B]
    [IsDomain A] [IsLocalRing A]
    [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B]
    [Module.IsTorsionFree A B] :
    IsPrincipalIdealRing B := by
  apply IsPrincipalIdealRing.of_finite_maximals
  refine
    (IsDedekindDomain.primesOver_finite
      (IsLocalRing.maximalIdeal A) B).subset ?_
  intro I hI
  letI : I.IsMaximal := hI
  have hunder : (I.under A).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal I
  have hover : IsLocalRing.maximalIdeal A = I.under A :=
    (IsLocalRing.eq_maximalIdeal hunder).symm
  exact ⟨hI.isPrime, ⟨hover⟩⟩
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
