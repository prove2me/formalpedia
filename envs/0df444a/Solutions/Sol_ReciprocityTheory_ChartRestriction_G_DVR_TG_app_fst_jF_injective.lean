-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TG.app_fst_jF_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:53.27612+00:00
-- url     : https://prove2.me/submissions/b98e5c35-3a64-4491-b2eb-b1d30d08488f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenFlat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_isDominant_jF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
noncomputable section
variable {R : Type} [CommRing R] [IsDomain R]
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
theorem _root_.solution {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] (U : X.Opens) :
    Function.Injective ((pullback.fst p (jF R)).app U) := by
  have := isDominant_jF R
  have : IsSchemeTheoreticallyDominant (jF R) := IsSchemeTheoreticallyDominant.of_isDominant _
  exact Scheme.Hom.app_injective _ U
end ReciprocityTheory.ChartRestriction.G.DVR.TG
