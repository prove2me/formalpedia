-- Prove2me | solution 1 for ReciprocityTheory.CA.height_le_height_comap_C_add_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:08:48.792247+00:00
-- url     : https://prove2.me/submissions/7032e51e-4ee4-40af-ad09-fadcc7b40886

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_IsSaturatedChain
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_AlgStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open Polynomial
namespace ReciprocityTheory.CA
theorem _root_.solution {R : Type*} [CommRing R] [IsNoetherianRing R]
    (P : Ideal R[X]) [P.IsPrime] : P.height ≤ (P.comap C).height + 1 := by

  set p := P.comap (C : R →+* R[X]) with hp
  letI : Algebra R[X] (Localization.AtPrime p)[X] := Polynomial.algebra R (Localization.AtPrime p)
  haveI : IsLocalization (Submonoid.map (C : R →+* R[X]) p.primeCompl)
      (Localization.AtPrime p)[X] := Polynomial.isLocalization p.primeCompl (Localization.AtPrime p)
  haveI : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl (Localization.AtPrime p) inferInstance
  have hd : Disjoint ((Submonoid.map (C : R →+* R[X]) p.primeCompl : Submonoid R[X]) :
      Set R[X]) (P : Set R[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsP
    exact hs hsP
  haveI hP' : (P.map (algebraMap R[X] (Localization.AtPrime p)[X])).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ P ‹P.IsPrime› hd
  have hcomap := IsLocalization.comap_map_of_isPrime_disjoint
    (Submonoid.map (C : R →+* R[X]) p.primeCompl) (Localization.AtPrime p)[X] ‹P.IsPrime› hd
  have hh : P.height = (P.map (algebraMap R[X] (Localization.AtPrime p)[X])).height :=
    (congrArg Ideal.height hcomap.symm).trans
      (IsLocalization.height_comap (Submonoid.map (C : R →+* R[X]) p.primeCompl) _)
  have h1 := Ideal.height_le_ringKrullDim_of_ne_top hP'.ne_top
  rw [Polynomial.ringKrullDim_of_isNoetherianRing,
    IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), ← hh] at h1
  exact_mod_cast h1
end ReciprocityTheory.CA
