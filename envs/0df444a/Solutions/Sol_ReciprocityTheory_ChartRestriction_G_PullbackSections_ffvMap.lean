-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.ffvMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:28:43.53666+00:00
-- url     : https://prove2.me/submissions/e3c6d574-7499-4530-803d-dbaad7fd79ba

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Mathlib.Algebra.MvPolynomial.Funext
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_FFVMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_rowInv_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_rowDeg_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_harmK_map

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open NumberField IsDedekindDomain Formalism.L2.Pj MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution : FFVMapSt0 := by
  intro E _ _ _ H Dw l c _ a n P hP T io
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hP
  have : CharZero T.Fr := charZero_of_injective_algebraMap (IsFractionRing.injective T.V T.Fr)
  have : Infinite c.F := Infinite.of_injective (fun m : ℕ => (m : c.F)) fun m m' h => by
    have := congrArg io h
    simpa using this
  refine ⟨⟨harmK_map io h1, rowInv_map io h2, rowDeg_map io h3⟩, fun m => ?_⟩
  rw [coeff_map]
  have hi : IsIntegral ℤ (P.coeff m) := h4 m
  obtain ⟨p, hpm, hp⟩ := hi
  have hV : IsIntegral T.V (io (P.coeff m)) := by
    refine ⟨p.map (Int.castRingHom T.V), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap T.V T.Fr).comp (Int.castRingHom T.V))
      (io.comp (algebraMap ℤ c.F)), ← Polynomial.hom_eval₂, hp, map_zero]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hV
  exact ⟨y, hy⟩
end ReciprocityTheory.ChartRestriction.G.PullbackSections
