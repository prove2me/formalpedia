-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.heightOnePlace_order_algebraMap_of_finrank_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:54:52.388504+00:00
-- url     : https://prove2.me/submissions/75ef6a97-9997-44ea-aab2-beb240ef7755

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
import Mathlib.RingTheory.DedekindDomain.Different
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_TrivialFieldExtension
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ramificationIdx_and_weakDifferent_of_finrank_eq_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOnePlace_order_algebraMap


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (B C K L : Type*) [CommRing B] [CommRing C] [Field K] [Field L]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [Algebra B C] [Algebra C L] [IsFractionRing C L] [IsScalarTower B C L]
    [Module.IsTorsionFree B C] [Module.Finite B C]
    [Algebra.IsSeparable K L]
include K L
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {k : Type*} [Field k] [Finite k] [Algebra k K] [Algebra k L]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (Q : IsDedekindDomain.HeightOneSpectrum C) [Q.asIdeal.LiesOver H.asIdeal]
    (hdegree : Module.finrank K L = 1) (x : K) :
    (heightOnePlace (k := k) (K := L) Q).order (algebraMap K L x) =
      (heightOnePlace (k := k) (K := K) H).order x := by
  by_cases hx : x = 0
  · simp [hx, GlobalPlace.order]
  · have he := (ramificationIdx_and_weakDifferent_of_finrank_eq_one
      B C K L H Q hdegree).1
    simpa only [he, Nat.cast_one, one_mul] using
      heightOnePlace_order_algebraMap (k := k) H Q x hx
end QEC.Coding.AlgebraicGeometry
