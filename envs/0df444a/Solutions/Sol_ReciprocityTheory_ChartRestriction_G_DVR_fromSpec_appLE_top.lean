-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.fromSpec_appLE_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:54:41.046958+00:00
-- url     : https://prove2.me/submissions/7027f295-e226-44b9-a467-f938c1075f9a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThickKer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {V : Type} [CommRing V] {X : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _
  exact (Spec Γ(X, U)).presheaf.map_id _
end ReciprocityTheory.ChartRestriction.G.DVR
