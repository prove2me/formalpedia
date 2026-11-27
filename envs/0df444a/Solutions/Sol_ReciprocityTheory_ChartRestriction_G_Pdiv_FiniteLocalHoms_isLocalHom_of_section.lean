-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms.isLocalHom_of_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:29:26.167435+00:00
-- url     : https://prove2.me/submissions/6d46d178-d1c0-41ba-8169-48dab84ed1c6

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
theorem _root_.solution (χ : R →ₐ[O] O) : IsLocalHom (χ : R →+* O) := by
  constructor
  intro r hr
  by_contra hnr
  obtain ⟨u, hu⟩ := hr
  have hu' : χ r = ↑u := hu.symm
  have h1 : χ (r * algebraMap O R (↑u⁻¹ : O)) = 1 := by
    rw [map_mul, AlgHom.commutes, hu', Algebra.algebraMap_self, RingHom.id_apply, Units.mul_inv]
  have h2 : IsUnit (1 - r * algebraMap O R (↑u⁻¹ : O)) := by
    apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
    exact mul_mem_nonunits_left hnr
  have h3 : χ (1 - r * algebraMap O R (↑u⁻¹ : O)) = 0 := by rw [map_sub, map_one, h1, sub_self]
  have h4 := h2.map χ
  rw [h3] at h4
  exact not_isUnit_zero h4
end ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms
