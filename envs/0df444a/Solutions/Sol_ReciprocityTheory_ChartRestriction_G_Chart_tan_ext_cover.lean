-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.tan_ext_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:24:25.428829+00:00
-- url     : https://prove2.me/submissions/6cc8ec85-5494-444f-9d88-c483223ed80e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_toL_comp


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
set_option backward.isDefEq.respectTransparency false
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {n : ℕ} (s : Fin n → S) (hs : Ideal.span (Set.range s) = ⊤)
    {v₁ v₂ : sp (R₀ := S) (DualNumber S) ⟶ G}
    (h : ∀ k, spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ v₁ =
      spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ v₂) : v₁ = v₂ := by
  have hs' : Ideal.span (Set.range (fun k => (TrivSqZeroExt.inl (s k) : DualNumber S))) = ⊤ := by
    have := congrArg (Ideal.map (TrivSqZeroExt.inlHom S S)) hs
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
    exact this
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of (DualNumber S)) _ hs').openCover
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext 𝒰 _ _ fun (k : Fin n) => ?_
  have e : 𝒰.f k = Spec.map (CommRingCat.ofHom (toL (s k))) ≫ Spec.map (CommRingCat.ofHom (dAway (s k))) := by
    show Spec.map (CommRingCat.ofHom (algebraMap (DualNumber S) (Ld (s k)))) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← toL_comp]
  rw [e, Category.assoc, Category.assoc]
  congr 1
  exact congrArg (fun q => Over.Hom.left q) (h k)
end ReciprocityTheory.ChartRestriction.G.Chart
