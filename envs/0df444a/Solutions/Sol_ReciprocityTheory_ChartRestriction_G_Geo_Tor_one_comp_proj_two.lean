-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.one_comp_proj_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:04:59.941631+00:00
-- url     : https://prove2.me/submissions/a4d08ba9-fcdb-4f53-853c-3cdd5b5351ff

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExtVCat

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
theorem _root_.solution (k : Fin 2) : (1 : 𝟙_ (Over S) ⟶ G2 G) ≫ x2 G k = 1 := by
  fin_cases k
  · show (1 : 𝟙_ (Over S) ⟶ G2 G) ≫ fst _ _ = 1
    exact MonObj.one_comp _
  · show (1 : 𝟙_ (Over S) ⟶ G2 G) ≫ snd _ _ = 1
    exact MonObj.one_comp _
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
