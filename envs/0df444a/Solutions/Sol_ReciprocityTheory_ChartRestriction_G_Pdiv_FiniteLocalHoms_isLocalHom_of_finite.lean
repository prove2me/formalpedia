-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms.isLocalHom_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:29:17.637478+00:00
-- url     : https://prove2.me/submissions/51dbbcec-c1f9-4cc4-b214-eb4f3486691a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_FiniteLocalLifts_IsLocalHomAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open IsLocalRing
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms
variable {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [IsLocalRing R] [Algebra O R]
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms
theorem _root_.solution [Module.Finite O R] {S : Type} [CommRing S] [IsLocalRing S] [Algebra O S]
    (hS : IsLocalHom (algebraMap O S)) (χ : R →ₐ[O] S) : IsLocalHom (χ : R →+* S) := by
  constructor
  intro r hr
  by_contra hnr
  have hcomap : Ideal.comap (algebraMap O R) (Ideal.comap (χ : R →+* S) (maximalIdeal S)) = maximalIdeal O := by
    rw [Ideal.comap_comap, AlgHom.comp_algebraMap]
    ext a
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff]
    exact ⟨fun h ha => h (ha.map _), fun h ha => h (hS.map_nonunit a ha)⟩
  have hmax : (Ideal.comap (χ : R →+* S) (maximalIdeal S)).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (by rw [hcomap]; infer_instance)
  have hPeq : Ideal.comap (χ : R →+* S) (maximalIdeal S) = maximalIdeal R := IsLocalRing.eq_maximalIdeal hmax
  have hrP : r ∈ Ideal.comap (χ : R →+* S) (maximalIdeal S) := by
    rw [hPeq]
    exact hnr
  exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp hrP) hr
end ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms
