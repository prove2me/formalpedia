-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.chart_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:05:54.356811+00:00
-- url     : https://prove2.me/submissions/e4e7ec60-b1e3-4903-ba32-21fc24c47139

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ChartAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanSRestrict
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pt_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_inj


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
variable {s : S} (C : Chart (Gs G s)) {A : Type} [CommRing A] [Algebra S A] [Algebra (Localization.Away s) A]
  [IsScalarTower S (Localization.Away s) A]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {h₁ h₂ : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A}
    (e : pushR G (pt C h₁) = pushR G (pt C h₂)) : h₁ = h₂ :=
  pt_injective C (pushR_inj (G := G) e)
end ReciprocityTheory.ChartRestriction.G.Chart
