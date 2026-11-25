-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.tanS_uniq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:49:12.719214+00:00
-- url     : https://prove2.me/submissions/6082d53b-ce08-444d-b0e3-e476305d0d6c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_toAlgHom_restrict
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_chart_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_chart_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_chart_scale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tanS_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tan_uniq


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
theorem _root_.solution {y₁ y₂ : sp (R₀ := S) (DualNumber A) ⟶ G} (h₁ : TanS y₁) (h₂ : TanS y₂)
    (he : spMap (dualMapS (IsScalarTower.toAlgHom S A A')) ≫ y₁ = spMap (dualMapS (IsScalarTower.toAlgHom S A A')) ≫ y₂) :
    ∃ m ∈ M, spMap (scaleS (S := S) (algebraMap (Localization.Away s) A m)) ≫ y₁ =
      spMap (scaleS (S := S) (algebraMap (Localization.Away s) A m)) ≫ y₂ := by
  obtain ⟨g₁, t₁, rfl⟩ := tanS_chart C h₁
  obtain ⟨g₂, t₂, rfl⟩ := tanS_chart C h₂
  rw [← toAlgHom_restrict (Localization.Away s) A A', chart_map, chart_map] at he
  obtain ⟨m, hm, hc⟩ := tan_uniq (epsA C A) M g₁ g₂ t₁ t₂ (chart_inj C he)
  exact ⟨m, hm, by rw [chart_scale, chart_scale, hc]⟩
end ReciprocityTheory.ChartRestriction.G.Chart
