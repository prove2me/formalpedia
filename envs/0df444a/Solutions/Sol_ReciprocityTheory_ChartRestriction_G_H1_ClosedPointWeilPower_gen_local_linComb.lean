-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower.gen_local_linComb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:33:00.526854+00:00
-- url     : https://prove2.me/submissions/ab1a7c01-36c0-46d6-b75c-a8e42220f6c0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ClosedPointWeilPower
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_ClosedPointWeilPower_gen_local
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_isLB


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.DVR TopologicalSpace
namespace ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower
theorem _root_.solution {V : Type} [CommRing V] [IsLocalRing V] {X : Scheme.{0}} (L : LB X)
    (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Spec (CommRingCat.of V) ⟶ X)) (ε : K → ℤ) :
    ∃ e : LB.Gen (LB.LinComb L φ ε), e.IsGen :=
  gen_local _ (by
    first
      | exact linComb_isLB
      | exact linComb_isLB hL
      | exact linComb_isLB (hL := hL)
      | exact linComb_isLB hL φ ε
      | exact linComb_isLB L hL φ ε
      | exact linComb_isLB (L := L) (φ := φ) (ε := ε) hL
      | exact linComb_isLB L φ ε hL)
end ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower
