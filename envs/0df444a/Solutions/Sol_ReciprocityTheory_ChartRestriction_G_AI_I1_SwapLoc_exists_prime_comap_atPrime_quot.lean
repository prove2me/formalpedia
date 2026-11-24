-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.exists_prime_comap_atPrime_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:10.87191+00:00
-- url     : https://prove2.me/submissions/d2ddb30a-6f08-4c53-8eec-2fdf65853f9e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
open ReciprocityTheory.ChartRestriction.G.AI
namespace ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
theorem _root_.solution {R : Type*} [CommRing R] (V Z : Ideal R)
    [(Z.map (Ideal.Quotient.mk V)).IsPrime] (Q : Ideal R) (hQ : Q.IsPrime) (hVQ : V ≤ Q)
    (hQZ : Q ≤ Z) :
    ∃ p : Ideal (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))), p.IsPrime ∧
      p.comap (algebraMap R _) = Q := by
  haveI := hQ
  haveI hQV : (Q.map (Ideal.Quotient.mk V)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hVQ)
  have hd : Disjoint ((Z.map (Ideal.Quotient.mk V)).primeCompl : Set (R ⧸ V))
      (Q.map (Ideal.Quotient.mk V) : Set (R ⧸ V)) :=
    Set.disjoint_left.2 fun x hx hxQ => hx (Ideal.map_mono hQZ hxQ)
  refine ⟨(Q.map (Ideal.Quotient.mk V)).map
      (algebraMap (R ⧸ V) (Localization.AtPrime (Z.map (Ideal.Quotient.mk V)))),
    IsLocalization.isPrime_of_isPrime_disjoint _ _ _ hQV hd, ?_⟩
  rw [IsScalarTower.algebraMap_eq R (R ⧸ V) (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))),
    ← Ideal.comap_comap]
  have hcm := IsLocalization.comap_map_of_isPrime_disjoint (Z.map (Ideal.Quotient.mk V)).primeCompl
    (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))) hQV hd
  rw [show Ideal.comap (algebraMap (R ⧸ V) (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))))
      (Ideal.map (algebraMap (R ⧸ V) (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))))
        (Q.map (Ideal.Quotient.mk V))) = Q.map (Ideal.Quotient.mk V) from hcm]
  rw [Ideal.Quotient.algebraMap_eq, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 hVQ]
end ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
