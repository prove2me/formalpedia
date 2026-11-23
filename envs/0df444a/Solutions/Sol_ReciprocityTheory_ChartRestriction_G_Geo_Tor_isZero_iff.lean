-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.isZero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:50.710906+00:00
-- url     : https://prove2.me/submissions/05a55ae8-3848-45d1-aea8-ca5a9ac30278

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (g : GtPtF D F) : g.IsZero ↔ g.b = 1 ∧ ∀ χ y J, Good D.P.L y J → val (g.s χ) (𝟙 _) y J = 1 := by
  constructor
  · rintro ⟨hb, hs⟩
    exact ⟨hb, fun χ y J hy => (val_corr (hJ := hy) (hs χ) (𝟙 _)).trans (val_one _)⟩
  · rintro ⟨hb, hs⟩
    exact ⟨hb, fun χ => corr_of_val D.P.isLB (fun y J hy => (hs χ y J hy).trans (val_one _).symm)⟩
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
