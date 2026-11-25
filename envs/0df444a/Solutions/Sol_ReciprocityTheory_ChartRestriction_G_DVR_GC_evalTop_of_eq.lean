-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.GC.evalTop_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:54:31.026273+00:00
-- url     : https://prove2.me/submissions/c00bc16e-7da7-4f16-a0ed-b6927f4c8fe4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_QuadTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_GC_evalTop_specMap

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.GC
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing
namespace ReciprocityTheory.ChartRestriction.G.DVR.GC
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (g : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) (hg : g = Spec.map (CommRingCat.ofHom f))
    (U : (Spec (CommRingCat.of A)).Opens) (hU : U = ⊤) (hU' : g ⁻¹ᵁ U = ⊤)
    (a : Γ(Spec (CommRingCat.of A), U)) :
    evalTop _ hU' ((g.app U).hom a) = f (evalTop U hU a) := by
  subst hg
  exact evalTop_specMap f U hU hU' a
end ReciprocityTheory.ChartRestriction.G.DVR.GC
