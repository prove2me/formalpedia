-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.differentIdeal_eq_top_of_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:31:17.203512+00:00
-- url     : https://prove2.me/submissions/2bc828ed-6e82-420b-abd4-f9fc027edc37

import Mathlib.RingTheory.DedekindDomain.Different
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_Transport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_differentIdeal_map_algEquiv_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
attribute [local instance] FractionRing.liftAlgebra
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsIntegrallyClosed A]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra A C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    (σ : B ≃ₐ[A] C)
    (hC : differentIdeal A C = ⊤) :
    differentIdeal A B = ⊤ := by
  exact (Ideal.map_eq_top_of_bijective
    (I := differentIdeal A B) σ.toRingHom σ.bijective).mp
      ((differentIdeal_map_algEquiv_eq A B C σ).trans hC)
end QEC.Coding.AlgebraicGeometry
