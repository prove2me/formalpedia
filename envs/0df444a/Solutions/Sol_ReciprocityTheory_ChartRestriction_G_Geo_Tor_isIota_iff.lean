-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.isIota_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:53.01593+00:00
-- url     : https://prove2.me/submissions/c5687264-6c46-43a0-974d-ccf400ed5a91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
theorem _root_.solution (x : D.X) (g : GtPtF D F) : GtPtF.IsIota x g ↔ g.b = cP D _ x ∧ ∀ χ y J, Good D.P.L y J →
    val (g.s χ) (𝟙 _) y J = val (D.tau x χ) (𝟙 _ ≫ jFK (R := R) F) y J := by
  constructor
  · rintro ⟨hb, hs⟩
    refine ⟨hb, fun χ y J hy => ?_⟩
    refine (val_corr (hJ := hy) (hs χ) _).trans ?_
    exact val_pull (hJ := hy) ..
  · rintro ⟨hb, hs⟩
    refine ⟨hb, fun χ => corr_of_val D.P.isLB (fun y J hy => ?_)⟩
    refine (hs χ y J hy).trans ?_
    exact (val_pull (hJ := hy) ..).symm
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
