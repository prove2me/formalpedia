-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ramificationIdx_and_weakDifferent_of_finrank_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:52:44.834319+00:00
-- url     : https://prove2.me/submissions/00b57486-8e52-479c-a730-295dce834a8a

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
import Mathlib.RingTheory.DedekindDomain.Different
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_TrivialFieldExtension
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_differentIdeal_eq_top_of_finrank_eq_one

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
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (Q : IsDedekindDomain.HeightOneSpectrum C) [Q.asIdeal.LiesOver H.asIdeal]
    (hdegree : Module.finrank K L = 1) :
    H.asIdeal.ramificationIdx' Q.asIdeal = 1 ∧
      multiplicity Q.asIdeal (differentIdeal B C) =
        2 * (H.asIdeal.ramificationIdx' Q.asIdeal - 1) := by
  letI : NoZeroSMulDivisors B C := ⟨fun {_ _} h => smul_eq_zero.mp h⟩
  letI : H.asIdeal.IsMaximal := H.isPrime.isMaximal H.ne_bot
  letI : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (by rw [hdegree]; norm_num)
  have hepos : H.asIdeal.ramificationIdx' Q.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver Q.asIdeal H.ne_bot
  have hele : H.asIdeal.ramificationIdx' Q.asIdeal ≤ 1 :=
    (Ideal.ramificationIdx_le_finrank C K L Q.asIdeal).trans_eq hdegree
  have he : H.asIdeal.ramificationIdx' Q.asIdeal = 1 := by omega
  refine ⟨he, ?_⟩
  rw [differentIdeal_eq_top_of_finrank_eq_one B C K L hdegree, he,
    Nat.sub_self, Nat.mul_zero]
  apply multiplicity_eq_zero.mpr
  rw [Ideal.dvd_iff_le]
  intro h
  exact Q.isPrime.ne_top (top_unique h)
end QEC.Coding.AlgebraicGeometry
