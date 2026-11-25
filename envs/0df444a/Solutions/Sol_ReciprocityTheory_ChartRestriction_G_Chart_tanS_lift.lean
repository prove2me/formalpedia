-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.tanS_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:53:54.386972+00:00
-- url     : https://prove2.me/submissions/ffdd1f89-8865-4b63-8570-00ef3c66794a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_toAlgHom_restrict
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_chart_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_chart_scale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_chart_tanS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tanS_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tan_lift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G] {s : S} (C : Chart (Gs G s))
  [Algebra.FinitePresentation (Localization.Away s) Γ((Gs G s).left, C.U)]
  {A : Type} [CommRing A] [Algebra S A] [Algebra (Localization.Away s) A] [IsScalarTower S (Localization.Away s) A]
  {A' : Type} [CommRing A'] [Algebra S A'] [Algebra (Localization.Away s) A'] [IsScalarTower S (Localization.Away s) A']
  [Algebra A A'] [IsScalarTower (Localization.Away s) A A'] [IsScalarTower S A A']
  (M : Submonoid (Localization.Away s)) [IsLocalization (Algebra.algebraMapSubmonoid A M) A']
include C
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {y' : sp (R₀ := S) (DualNumber A') ⟶ G} (hy' : TanS y') :
    ∃ m ∈ M, ∃ y : sp (R₀ := S) (DualNumber A) ⟶ G, TanS y ∧
      spMap (dualMapS (IsScalarTower.toAlgHom S A A')) ≫ y =
        spMap (scaleS (S := S) (algebraMap (Localization.Away s) A' m)) ≫ y' := by
  obtain ⟨h', hh', rfl⟩ := tanS_chart C hy'
  have hh'' : IsTanAt ((IsScalarTower.toAlgHom (Localization.Away s) A A').comp (epsA C A)) h' := by
    intro b
    rw [hh' b]
    show algebraMap (Localization.Away s) A' (eps C b) = algebraMap A A' (algebraMap (Localization.Away s) A (eps C b))
    exact IsScalarTower.algebraMap_apply _ _ _ _
  obtain ⟨m, hm, h, hh, he⟩ := tan_lift (epsA C A) M h' hh''
  refine ⟨m, hm, pushR G (pt C h), chart_tanS C h hh, ?_⟩
  rw [← toAlgHom_restrict (Localization.Away s) A A', chart_map, he, chart_scale]
end ReciprocityTheory.ChartRestriction.G.Chart
