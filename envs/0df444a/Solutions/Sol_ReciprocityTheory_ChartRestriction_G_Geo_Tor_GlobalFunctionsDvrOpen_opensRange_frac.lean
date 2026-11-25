-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen.opensRange_frac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:01:23.328773+00:00
-- url     : https://prove2.me/submissions/b4796163-8f3e-4307-a7d8-a555d8c8d9c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobFnsDvr
import Definitions.Def_Lemmata_GeneralBFactFurther_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobalFunctionsDvrOpen

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen
variable {V : Type} [CommRing V] [IsDomain V]
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen
theorem _root_.solution [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ) :
    haveI := isOpenImmersion_frac hϖ
    (spMap (algebraMap V (FractionRing V))).opensRange =
      (Sp V).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of V)).inv ϖ) := by
  have := isLocalization_frac hϖ
  rw [basicOpen_eq_of_affine]
  ext1
  exact PrimeSpectrum.localization_away_comap_range (FractionRing V) ϖ
end ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen
