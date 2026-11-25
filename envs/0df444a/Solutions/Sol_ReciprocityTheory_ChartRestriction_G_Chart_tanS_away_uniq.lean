-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.tanS_away_uniq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:10:49.905256+00:00
-- url     : https://prove2.me/submissions/25d714f0-e576-4940-97ff-a02ce1c79107

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ScalePowMono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_fp_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tanS_uniq


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
variable [∀ s : S, Smooth (Gs G s).hom]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {s : S} (C : Chart (Gs G s)) {A : Type} [CommRing A] [Algebra S A]
    [Algebra (Localization.Away s) A] [IsScalarTower S (Localization.Away s) A] (t : S)
    {y₁ y₂ : sp (R₀ := S) (DualNumber A) ⟶ G} (h₁ : TanS y₁) (h₂ : TanS y₂)
    (he : spMap (dualMapS (IsScalarTower.toAlgHom S A (Localization.Away (algebraMap S A t)))) ≫ y₁ =
      spMap (dualMapS (IsScalarTower.toAlgHom S A (Localization.Away (algebraMap S A t)))) ≫ y₂) :
    ∃ N : ℕ, spMap (scaleS (S := S) (algebraMap S A t ^ N)) ≫ y₁ = spMap (scaleS (algebraMap S A t ^ N)) ≫ y₂ := by
  haveI := fp_chart C
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A
      (Submonoid.powers (algebraMap S (Localization.Away s) t)))
      (Localization.Away (algebraMap S A t)) := by
    have e : Algebra.algebraMapSubmonoid A (Submonoid.powers (algebraMap S (Localization.Away s) t)) =
        Submonoid.powers (algebraMap S A t) := by
      rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, ← IsScalarTower.algebraMap_apply]
    rw [e]
    infer_instance
  obtain ⟨m, hm, heq⟩ := tanS_uniq C (A := A) (A' := Localization.Away (algebraMap S A t))
    (Submonoid.powers (algebraMap S (Localization.Away s) t)) h₁ h₂ he
  obtain ⟨N, rfl⟩ := hm
  refine ⟨N, ?_⟩
  rw [map_pow, ← IsScalarTower.algebraMap_apply] at heq
  exact heq
end ReciprocityTheory.ChartRestriction.G.Chart
