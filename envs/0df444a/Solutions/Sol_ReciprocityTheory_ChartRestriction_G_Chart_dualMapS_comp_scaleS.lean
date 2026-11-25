-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.dualMapS_comp_scaleS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:12:14.665285+00:00
-- url     : https://prove2.me/submissions/13fa15f3-87d0-42c6-8ad4-9e18d4e6d8b4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
import Theorems.Thm_Bl_FirstBlockLemmaK_goal1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
section Wrap
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G] {s : S} (C : Chart (Gs G s))
  [Algebra.FinitePresentation (Localization.Away s) Γ((Gs G s).left, C.U)]
  {A : Type} [CommRing A] [Algebra S A] [Algebra (Localization.Away s) A] [IsScalarTower S (Localization.Away s) A]
  {A' : Type} [CommRing A'] [Algebra S A'] [Algebra (Localization.Away s) A'] [IsScalarTower S (Localization.Away s) A']
  [Algebra A A'] [IsScalarTower (Localization.Away s) A A'] [IsScalarTower S A A']
  (M : Submonoid (Localization.Away s)) [IsLocalization (Algebra.algebraMapSubmonoid A M) A']
end Wrap
section Scale
variable {S : Type} [CommRing S]
private theorem dualMapS_fst' {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A']
    (j : A →ₐ[S] A') (y : DualNumber A) : (dualMapS j y).fst = j y.fst := by
  simp [dualMapS, Bl.ThirdBlockLemmaB.goal1, TrivSqZeroExt.lift_def]
private theorem dualMapS_snd' {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A']
    (j : A →ₐ[S] A') (y : DualNumber A) : (dualMapS j y).snd = j y.snd := by
  simp [dualMapS, Bl.ThirdBlockLemmaB.goal1, TrivSqZeroExt.lift_def]
private theorem scaleS_fst' {A : Type} [CommRing A] [Algebra S A] (c : A) (y : DualNumber A) :
    (scaleS (S := S) c y).fst = y.fst := by
  simp [scaleS]
private theorem scaleS_snd' {A : Type} [CommRing A] [Algebra S A] (c : A) (y : DualNumber A) :
    (scaleS (S := S) c y).snd = c * y.snd := by
  simp [scaleS]
variable {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
end Scale
section Over
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
end Over
end ReciprocityTheory.ChartRestriction.G.Chart
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (j : A →ₐ[S] A')
    (c : A) : (dualMapS j).comp (scaleS c) = (scaleS (j c)).comp (dualMapS j) := by
  refine AlgHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, dualMapS_fst', scaleS_fst', scaleS_fst',
      dualMapS_fst']
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, dualMapS_snd', scaleS_snd', scaleS_snd',
      dualMapS_snd', map_mul]
end ReciprocityTheory.ChartRestriction.G.Chart
