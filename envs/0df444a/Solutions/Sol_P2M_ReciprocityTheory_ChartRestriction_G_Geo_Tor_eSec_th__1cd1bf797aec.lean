-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_eSec_th__1cd1bf797aec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:32:27.806424+00:00
-- url     : https://prove2.me/submissions/8a489138-e3f2-4375-a91a-a0c4a8cc70ae

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExtVCat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_eta_eq_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_comp_psum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_psum_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_one_comp_proj_three

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (I : thK) : eSec (G3 G) ≫ thφ G (x3 G) I = eSec G := by
  show (η[G3 G]).left ≫ (psum G (x3 G) I.down).left = (η[G]).left
  rw [← Over.comp_left, eta_eq_one, eta_eq_one, comp_psum]
  simp only [one_comp_proj_three]
  rw [psum_one]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
