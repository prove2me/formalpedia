-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.GC.evalTop_pullGen_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:05:56.951102+00:00
-- url     : https://prove2.me/submissions/6883ab84-0cdb-4658-9b69-728ce709007c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_QuadTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_GC_evalTop_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_GC_evalTop_of_eq

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
    {X : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Spec (CommRingCat.of A) ⟶ X)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L φ ε)) (j : K → L.ι) (hU : LB.wchart L φ j = ⊤)
    (hU' : LB.wchart L (fun k => g ≫ φ k) j = ⊤) :
    evalTop _ hU' ((LB.pullGen L φ ε c g).s j).val = f (evalTop _ hU (c.s j).val) := by
  have hW : g ⁻¹ᵁ LB.wchart L φ j = ⊤ := by rw [hU, Scheme.Hom.preimage_top]
  have h1 := evalTop_res ((fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) :
    LB.wchart L (fun k => g ≫ φ k) j ≤ g ⁻¹ᵁ LB.wchart L φ j) hW hU' ((g.app _).hom (c.s j).val)
  exact h1.trans (evalTop_of_eq f g hg _ hU hW _)
end ReciprocityTheory.ChartRestriction.G.DVR.GC
