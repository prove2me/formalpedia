-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_C_charOf_mem_ae3c5b4eba75
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:52:56.234854+00:00
-- url     : https://prove2.me/submissions/790ba62e-4ac3-446a-ad44-556075ce5eff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_GeoNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PGeoNumCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial GroundTheory.Heights₂.Heights.Bridge GroundTheory.Heights₂.Heights.Bridge.GeoNum
  GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (V : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)) :
    (C ((ReciprocityTheory.ChartRestriction.G.Geo.charOf V : ℕ) : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) ∈ V := by
  have h : ((ReciprocityTheory.ChartRestriction.G.Geo.charOf V : ℕ) : ℤ) ∈
      V.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) := by
    rw [← Submodule.IsPrincipal.span_singleton_generator (V.comap C), Ideal.mem_span_singleton]
    exact Int.dvd_natAbs.mpr dvd_rfl
  exact h
end GroundTheory.Heights₂.Heights.Inter
