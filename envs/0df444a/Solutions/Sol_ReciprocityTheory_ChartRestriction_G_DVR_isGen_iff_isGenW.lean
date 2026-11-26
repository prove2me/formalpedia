-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.isGen_iff_isGenW
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:40:14.919447+00:00
-- url     : https://prove2.me/submissions/3d23d2d2-5b37-40df-a6a1-6a9fa1341ac9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage




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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
theorem _root_.solution {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L ψ ε)) : t.IsGen ↔ IsGenW L ψ ε t.s := by
  first
    | (intros; rfl)
    | exact Iff.rfl
    | decide
    | (intros; omega)
    | (intros; simp)
    | (intros; simp_all)
    | (intros; norm_num)
    | (intros; positivity)
    | (intros; aesop)
    | (intros; nlinarith)
    | (intros; field_simp; ring)
    | (intros; ext; simp)
    | (intros; constructor <;> intro h <;> simpa using h)
    | (intros; exact?)
  trace "HIT_47_1"

end 
