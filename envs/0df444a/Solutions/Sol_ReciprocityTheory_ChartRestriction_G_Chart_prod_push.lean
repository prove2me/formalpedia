-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.prod_push
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:41:24.212713+00:00
-- url     : https://prove2.me/submissions/ba34c3c9-90ba-4cf0-99b8-bc9ca37638ea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LiePush
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
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
theorem _root_.solution {n : ℕ} {T : Over (Sp S)} (u : Fin n → (T ⟶ G')) :
    (List.ofFn u).prod.left ≫ φ = (List.ofFn fun i => pushPt h.1.w (u i)).prod.left := by
  have hmul : ∀ a b : T ⟶ G', pushPt h.1.w (a * b) = pushPt h.1.w a * pushPt h.1.w b := fun a b =>
    Over.OverMorphism.ext (h.2 T a b (pushPt h.1.w a) (pushPt h.1.w b) rfl rfl).symm
  have hone : pushPt h.1.w (1 : T ⟶ G') = 1 := by
    have e1 : pushPt h.1.w (1 : T ⟶ G') * pushPt h.1.w 1 = pushPt h.1.w 1 := by
      rw [← hmul, _root_.one_mul]
    exact mul_right_cancel (e1.trans (_root_.one_mul _).symm)
  have key : ∀ {m : ℕ} (v : Fin m → (T ⟶ G')),
      pushPt h.1.w (List.ofFn v).prod = (List.ofFn fun i => pushPt h.1.w (v i)).prod := by
    intro m
    induction m with
    | zero => intro v; simp only [List.ofFn_zero, List.prod_nil]; exact hone
    | succ m ih => intro v; simp only [List.ofFn_succ, List.prod_cons]; rw [hmul, ih]
  exact congrArg (fun f => f.left) (key u)
end ReciprocityTheory.ChartRestriction.G.Chart
