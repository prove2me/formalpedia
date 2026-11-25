-- Prove2me | solution 1 for ReciprocityTheory.CA.height_le_one_of_comap_C_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:08:51.098488+00:00
-- url     : https://prove2.me/submissions/ab27c407-f0e5-47fa-9ae1-828d0d7869d3

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
attribute [local instance] Polynomial.algebra Polynomial.isLocalization
namespace ReciprocityTheory.CA
theorem _root_.solution {A : Type*} [CommRing A] [IsDomain A]
    (Q : Ideal A[X]) [Q.IsPrime] (hQ : Q.comap C = ⊥) : Q.height ≤ 1 := by

  have hd : Disjoint ((Submonoid.map (C : A →+* A[X]) (nonZeroDivisors A) : Submonoid A[X]) :
      Set A[X]) (Q : Set A[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsQ
    have h0 : s ∈ Q.comap C := hsQ
    rw [hQ, Ideal.mem_bot] at h0
    exact nonZeroDivisors.ne_zero hs h0
  haveI hQ' : (Q.map (algebraMap A[X] (FractionRing A)[X])).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ Q ‹Q.IsPrime› hd
  have hcomap := IsLocalization.comap_map_of_isPrime_disjoint
    (Submonoid.map (C : A →+* A[X]) (nonZeroDivisors A)) (FractionRing A)[X] ‹Q.IsPrime› hd
  have hh : Q.height = (Q.map (algebraMap A[X] (FractionRing A)[X])).height :=
    (congrArg Ideal.height hcomap.symm).trans
      (IsLocalization.height_comap (Submonoid.map (C : A →+* A[X]) (nonZeroDivisors A)) _)
  have h1 := Ideal.height_le_ringKrullDim_of_ne_top hQ'.ne_top
  rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    ← hh] at h1
  exact_mod_cast h1
end ReciprocityTheory.CA
