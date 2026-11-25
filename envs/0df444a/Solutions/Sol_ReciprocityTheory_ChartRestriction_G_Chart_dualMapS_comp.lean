-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.dualMapS_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:12:19.902906+00:00
-- url     : https://prove2.me/submissions/e68f9c43-3233-4beb-bb77-31d89760af57

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
theorem _root_.solution {A A' A'' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] [CommRing A'']
    [Algebra S A''] (j : A →ₐ[S] A') (j' : A' →ₐ[S] A'') : (dualMapS j').comp (dualMapS j) = dualMapS (j'.comp j) := by
  refine AlgHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · rw [AlgHom.comp_apply, dualMapS_fst', dualMapS_fst', dualMapS_fst', AlgHom.comp_apply]
  · rw [AlgHom.comp_apply, dualMapS_snd', dualMapS_snd', dualMapS_snd', AlgHom.comp_apply]
end ReciprocityTheory.ChartRestriction.G.Chart
