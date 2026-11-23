-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_O__comp_24bcd133e28a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:45.273982+00:00
-- url     : https://prove2.me/submissions/40fbdad3-7fc0-491e-8432-d68d4706da9c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WchartPullLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct

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
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.WeightPf
open Semi
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
omit [IsCommMonObj G]
namespace ReciprocityTheory.ChartRestriction.G.Out.WeightPf
theorem _root_.solution {T T' : Over (Spec (CommRingCat.of R))} (h : T' ⟶ T) (p : T ⟶ D.P.A) (χ : D.X)
    (k : Fin 4) : h.left ≫ D.Oφ p χ k = D.Oφ (h ≫ p) χ k := by
  have hu : h ≫ toUnit T = toUnit T' := toUnit_unique _ _
  fin_cases k
  · change h.left ≫ (padd D.P.A p (toUnit T ≫ D.c χ)).left = (padd D.P.A (h ≫ p) (toUnit T' ≫ D.c χ)).left
    rw [← Over.comp_left]
    congr 1
    simp only [padd]
    rw [← Category.assoc, CartesianMonoidalCategory.comp_lift, reassoc_of% hu]
  · change h.left ≫ (toUnit T ≫ D.c χ).left = (toUnit T' ≫ D.c χ).left
    rw [← Over.comp_left, ← Category.assoc, hu]
  · change h.left ≫ p.left = (h ≫ p).left
    rw [Over.comp_left]
  · change h.left ≫ (toUnit T ≫ η[D.P.A]).left = (toUnit T' ≫ η[D.P.A]).left
    rw [← Over.comp_left, ← Category.assoc, hu]
end ReciprocityTheory.ChartRestriction.G.Out.WeightPf
