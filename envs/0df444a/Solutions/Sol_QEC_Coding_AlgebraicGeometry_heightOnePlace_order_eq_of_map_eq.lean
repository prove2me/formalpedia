-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.heightOnePlace_order_eq_of_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:32:53.564134+00:00
-- url     : https://prove2.me/submissions/23b7774d-cb87-4970-ba0f-4407d421f716

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrderTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOnePlace_order_algebraMap


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {k R S L : Type*} [Field k] [Finite k]
    [CommRing R] [CommRing S] [Field L]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra k L] [Algebra R L] [Algebra S L]
    [IsFractionRing R L] [IsFractionRing S L]
    [Algebra R S] [FaithfulSMul R S] [IsScalarTower R S L]
    (H : IsDedekindDomain.HeightOneSpectrum R)
    (J : IsDedekindDomain.HeightOneSpectrum S) [J.asIdeal.LiesOver H.asIdeal]
    (hmap : Ideal.map (algebraMap R S) H.asIdeal = J.asIdeal) (x : L) :
    (heightOnePlace (k := k) (K := L) H).order x =
      (heightOnePlace (k := k) (K := L) J).order x := by
  have he : H.asIdeal.ramificationIdx' J.asIdeal = 1 := by
    have htop : Ideal.map (algebraMap R S) H.asIdeal ≠ ⊤ := by
      rw [hmap]
      exact J.isPrime.ne_top
    have hbot : Ideal.map (algebraMap R S) H.asIdeal ≠ ⊥ := by
      rw [hmap]
      exact J.ne_bot
    have h := H.asIdeal.ramificationIdx_map_self_eq_one htop hbot
    rwa [hmap] at h
  by_cases hx : x = 0
  · simp [hx, GlobalPlace.order]
  · have h := heightOnePlace_order_algebraMap (k := k) (K := L) (L := L) H J x hx
    simpa only [Algebra.algebraMap_self, RingHom.id_apply, he, Nat.cast_one, one_mul] using h.symm
end QEC.Coding.AlgebraicGeometry
