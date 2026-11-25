-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.comb_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:58:41.415671+00:00
-- url     : https://prove2.me/submissions/1a086712-0016-43b3-8f6f-3c0f45f6e691

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LiePush
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_inj_over
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_prod_push
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
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
omit h
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {R : Type} [CommRing R] {G₀ : Over (Sp R)} [GrpObj G₀] (f : R →+* S) {ψ : G'.left ⟶ G₀.left}
    (h : IsGrpPullback G' G₀ (Geo.Tor.spMap f) ψ) {n : ℕ} {c : Fin n → R} {v : Fin n → (epsR R ⟶ G₀)} {w : epsR R ⟶ G₀}
    (hc : IsLieComb c v w) {v' : Fin n → (epsR S ⟶ G')} {w' : epsR S ⟶ G'}
    (hv : ∀ i, (v' i).left ≫ ψ = Geo.Tor.spMap (dualMapR f) ≫ (v i).left)
    (hw : w'.left ≫ ψ = Geo.Tor.spMap (dualMapR f) ≫ w.left) : IsLieComb (fun i => f (c i)) v' w' := by
  obtain ⟨u, hu, rfl⟩ := hc
  have hs : ∀ s : S, Geo.Tor.spMap (epsScaleR s) ≫ (epsR S).hom = (epsR S).hom := by
    intro s
    simp only [epsR, Over.mk_hom, Geo.Tor.spMap, ← Spec.map_comp]
    congr 1
    ext r <;> first | simp [epsScaleR] | simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have hd : Geo.Tor.spMap (dualMapR f) ≫ (epsR R).hom = (epsR S).hom ≫ Geo.Tor.spMap f := by
    simp only [epsR, Over.mk_hom, Geo.Tor.spMap, ← Spec.map_comp]
    congr 1
    ext r <;> first
      | (simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl]; done)
      | (simp [dualMapR]; done)
      | simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl]
  have hcomm : ∀ i, Geo.Tor.spMap (dualMapR f) ≫ Geo.Tor.spMap (epsScaleR (c i)) =
      Geo.Tor.spMap (epsScaleR (f (c i))) ≫ Geo.Tor.spMap (dualMapR f) := by
    intro i
    simp only [Geo.Tor.spMap, ← Spec.map_comp]
    congr 1
    ext a <;> first
      | (simp [dualMapR, epsScaleR]; done)
      | (simp [dualMapR, epsScaleR, smul_eq_mul, map_mul]; done)
      | (simp [dualMapR, epsScaleR, smul_eq_mul, map_mul, mul_comm]; done)
      | (simp [dualMapR, epsScaleR, smul_eq_mul, map_mul, TrivSqZeroExt.algebraMap_eq_inl]; done)
      | (simp [dualMapR, epsScaleR, smul_eq_mul, TrivSqZeroExt.algebraMap_eq_inl]; clear * -; done)
  let d : Over.mk ((epsR S).hom ≫ Geo.Tor.spMap f) ⟶ epsR R := Over.homMk (Geo.Tor.spMap (dualMapR f)) hd
  have cm : ∀ a b : epsR R ⟶ G₀, d ≫ (a * b) = (d ≫ a) * (d ≫ b) := fun a b => by
    show d ≫ (lift a b ≫ μ) = lift (d ≫ a) (d ≫ b) ≫ μ
    rw [comp_lift_assoc]
  have c1 : d ≫ (1 : epsR R ⟶ G₀) = 1 := by
    show d ≫ (toUnit _ ≫ η) = toUnit _ ≫ η
    rw [comp_toUnit_assoc]
  have key : ∀ {m : ℕ} (a : Fin m → (epsR R ⟶ G₀)),
      d ≫ (List.ofFn a).prod = (List.ofFn fun i => d ≫ a i).prod := by
    intro m
    induction m with
    | zero => intro a; simp only [List.ofFn_zero, List.prod_nil]; exact c1
    | succ m ih => intro a; simp only [List.ofFn_succ, List.prod_cons]; rw [cm, ih]
  let u' : Fin n → (epsR S ⟶ G') := fun i =>
    Over.homMk (Geo.Tor.spMap (epsScaleR (f (c i))) ≫ (v' i).left)
      (by rw [Category.assoc, Over.w (v' i)]; exact hs _)
  have e2 : (fun i => d ≫ u i) = fun i => pushPt h.1.w (u' i) := by
    funext i
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, d, Over.homMk_left, pushPt, u', hu i, Category.assoc, hv i]
    rw [← Category.assoc, hcomm i, Category.assoc]
  refine ⟨u', fun i => rfl, ?_⟩
  apply inj_over h
  rw [hw, prod_push h u']
  show (d ≫ (List.ofFn u).prod).left = _
  rw [key, e2]
end ReciprocityTheory.ChartRestriction.G.Chart
