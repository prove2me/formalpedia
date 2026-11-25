-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.tanS_away_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:08:49.93312+00:00
-- url     : https://prove2.me/submissions/8224a93e-d32e-44e4-8b03-ef2a7d5a7034

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ScalePowMono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_fp_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tanS_lift


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
    {y' : sp (R₀ := S) (DualNumber (Localization.Away (algebraMap S A t))) ⟶ G} (hy' : TanS y') :
    ∃ N : ℕ, ∃ y : sp (R₀ := S) (DualNumber A) ⟶ G, TanS y ∧
      spMap (dualMapS (IsScalarTower.toAlgHom S A (Localization.Away (algebraMap S A t)))) ≫ y =
        spMap (scaleS (S := S) (algebraMap S (Localization.Away (algebraMap S A t)) t ^ N)) ≫ y' := by
  haveI := fp_chart C
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A
      (Submonoid.powers (algebraMap S (Localization.Away s) t)))
      (Localization.Away (algebraMap S A t)) := by
    have e : Algebra.algebraMapSubmonoid A (Submonoid.powers (algebraMap S (Localization.Away s) t)) =
        Submonoid.powers (algebraMap S A t) := by
      rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, ← IsScalarTower.algebraMap_apply]
    rw [e]
    infer_instance
  obtain ⟨m, hm, y, hy, heq⟩ := tanS_lift C (A := A) (A' := Localization.Away (algebraMap S A t))
    (Submonoid.powers (algebraMap S (Localization.Away s) t)) hy'
  obtain ⟨N, rfl⟩ := hm
  refine ⟨N, y, hy, ?_⟩
  rw [heq, map_pow, ← IsScalarTower.algebraMap_apply]
end ReciprocityTheory.ChartRestriction.G.Chart
