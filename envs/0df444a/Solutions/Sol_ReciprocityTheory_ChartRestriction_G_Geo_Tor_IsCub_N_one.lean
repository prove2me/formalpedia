-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub.N_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:00.474984+00:00
-- url     : https://prove2.me/submissions/813c4616-5e12-46ec-a4fe-6f414daa89a4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__944b82dcaa95

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
open ReciprocityTheory.ChartRestriction.G.Semi
variable {A U : Type} [CommGroup A] [CommGroup U]
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub
variable {θ : A → A → A → U} (h : IsCub θ)
include h
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub
theorem _root_.solution (k : ℕ) (a m : A) : cubN θ k a m 1 = 1 := Finset.prod_eq_one fun _ _ => h.face₃ _ _
end ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub
