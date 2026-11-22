-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pullU_res__268497da66fb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:02.900811+00:00
-- url     : https://prove2.me/submissions/3fab3b39-97a1-4e48-869d-39d999846094

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} {E : SplitExt S} {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂]
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {X Y : Scheme.{0}} (f : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U) (u : Γ(Y, U)ˣ) :
    pullU f V (res h u) = res (f.preimage_mono h) (pullU f U u) := by
  apply Units.ext
  have := congrArg (fun φ => φ.hom u.val) (f.naturality (homOfLE h).op)
  simpa [pullU, res] using this
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
