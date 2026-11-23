-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.mem_finf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:44.740329+00:00
-- url     : https://prove2.me/submissions/294348f1-0199-489c-8858-8b72b5fbf700

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {X : Scheme.{0}} {K : Type} (S : Finset K) (W : K → X.Opens) (x : X) (h : ∀ a ∈ S, x ∈ W a) :
    x ∈ S.inf W := by
  classical
  induction S using Finset.induction_on with
  | empty => trivial
  | insert a S _ ih =>
    rw [Finset.inf_insert]
    exact ⟨h a (Finset.mem_insert_self _ _), ih fun b hb => h b (Finset.mem_insert_of_mem hb)⟩
end ReciprocityTheory.ChartRestriction.G.DVR
