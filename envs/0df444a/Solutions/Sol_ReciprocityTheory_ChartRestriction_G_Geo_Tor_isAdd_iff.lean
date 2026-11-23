-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.isAdd_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:45.507111+00:00
-- url     : https://prove2.me/submissions/2fcefc48-d0de-4a31-a40f-bb313026000d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cubAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr


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
theorem _root_.solution (g g' g'' : GtPtF D F) : g.IsAdd g' g'' ↔ g''.b = g.b * g'.b ∧ ∀ χ y J, Good D.P.L y J →
    val (g''.s χ) (𝟙 _) y J * th D y J (cP D _ χ) g.b g'.b = val (g.s χ) (𝟙 _) y J * val (g'.s χ) (𝟙 _) y J := by
  constructor
  · rintro ⟨hb, hs⟩
    refine ⟨hb, fun χ y J hy => ?_⟩
    rw [← val_cubAt hy]
    refine (val_mul (hJ := hy) ..).symm.trans ?_
    refine (val_corr (hJ := hy) (hs χ) _).trans ?_
    exact val_mul (hJ := hy) ..
  · rintro ⟨hb, hs⟩
    refine ⟨hb, fun χ => corr_of_val D.P.isLB (fun y J hy => ?_)⟩
    refine (val_mul (hJ := hy) ..).trans ?_
    refine Eq.trans ?_ (val_mul (hJ := hy) ..).symm
    rw [val_cubAt hy]
    exact hs χ y J hy
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
