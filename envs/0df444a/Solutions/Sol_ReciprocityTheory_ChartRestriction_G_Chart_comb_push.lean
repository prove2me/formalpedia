-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.comb_push
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:06:57.380798+00:00
-- url     : https://prove2.me/submissions/c10917c8-7c34-4ddd-bba1-aa19a5f3bd14

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LiePush
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_inj_over
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_prod_push
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp
open scoped CategoryTheory.Obj
variable {S : Type} [CommRing S] {X : Scheme.{0}} {x : Sp S ⟶ X} {G : Over X} {G' : Over (Sp S)} [GrpObj G] [GrpObj G']
  {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ)
include h
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {n : ℕ} (c : Fin n → S) (v : Fin n → (epsR S ⟶ G')) (w : epsR S ⟶ G') : IsLieComb c v w ↔
    ∃ u : Fin n → (Over.mk (Geo.Tor.spMap (algebraMap S (DualNumber S)) ≫ x) ⟶ G),
      (∀ i, (u i).left = Geo.Tor.spMap (epsScaleR (c i)) ≫ (v i).left ≫ φ) ∧ (List.ofFn u).prod.left = w.left ≫ φ := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => pushPt h.1.w (u i), fun i => ?_, (prod_push h u).symm⟩
    simp [pushPt, hu i]
  · rintro ⟨u, hu, hw⟩
    have hs : ∀ i, Geo.Tor.spMap (epsScaleR (c i)) ≫ (epsR S).hom = (epsR S).hom := by
      intro i
      simp only [epsR, Over.mk_hom, Geo.Tor.spMap, ← Spec.map_comp]
      congr 1
      ext r <;> first | simp [epsScaleR] | simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
    let u' : Fin n → (epsR S ⟶ G') := fun i =>
      Over.homMk (Geo.Tor.spMap (epsScaleR (c i)) ≫ (v i).left) (by rw [Category.assoc, Over.w (v i)]; exact hs i)
    refine ⟨u', fun i => rfl, ?_⟩
    apply inj_over h
    have e : (fun i => pushPt h.1.w (u' i)) = u :=
      funext fun i => Over.OverMorphism.ext (by simp [pushPt, u', hu i])
    rw [prod_push h u', ← hw, e]
end ReciprocityTheory.ChartRestriction.G.Chart
