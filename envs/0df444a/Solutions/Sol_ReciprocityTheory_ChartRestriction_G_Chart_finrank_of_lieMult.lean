-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.finrank_of_lieMult
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:26:38.624798+00:00
-- url     : https://prove2.me/submissions/bbbdf959-abd1-48f6-92b8-bb4a56a311b1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_inj
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_list_prod_tan__79ee0da3542e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_mem_eigLat_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_eig_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_eq_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_eig_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_exists_v
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_exists_w
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_pre
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_uniq_v
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_scale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_spec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : Geo.Tor.IsGrpPullback G' G f F) {k : Type} [Field k] {tk : Spec (CommRingCat.of k) ⟶ S'}
  {g : Spec (CommRingCat.of k) ⟶ S} (hg : tk ≫ f = g)
variable {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := k) (JetR k (Fin n) m) ⟶ (Over.pullback g).obj G} (hx : IsUnivChart _ n x)
  {O : Type} [CommRing O] (act : Geo.Tor.OAct O G') (b : O → (G ⟶ G))
  (hab : ∀ a, (act.act a).left ≫ F = F ≫ (b a).left)
  (act' : O → ((Over.pullback g).obj G ⟶ (Over.pullback g).obj G)) [∀ a, IsMonHom (act' a)]
  (hact' : ∀ a, act' a = (Over.pullback g).map (b a)) (τ : O →+* k)
include hc hg hab hact'
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {N : ℕ} (hL : Geo.Tor.LieMult act tk τ N) :
    Module.finrank k (eigLat hx act' (fun a => τ a)) = N := by
  obtain ⟨vB, hvB, huq⟩ := hL
  have hT : ∀ (w : viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G') v, Rel (F := F) tk g w v →
      (Geo.Tor.IsLieEigen act tk τ w ↔ IsTan v ∧ ∀ a, v ≫ act' a = spMap (scaleD (τ a)) ≫ v) := by
    intro w v h
    refine and_congr (tan_iff hc hg h) (forall_congr' fun a => ?_)
    rw [hact']
    exact eig_iff hc (act.act a) (b a) (hab a) (τ a) h
  choose v' hv' using fun i => rel_exists_v hc hg (X := sp (R₀ := k) (DualNumber k)) (vB i)
  have hv'e : ∀ i, IsTan (v' i) ∧ ∀ a, v' i ≫ act' a = spMap (scaleD (τ a)) ≫ v' i :=
    fun i => (hT _ _ (hv' i)).mp (hvB i)
  let bb : Fin N → Fin n → k := fun i => tcoord hx (v' i) (hv'e i).1
  have htv : ∀ i, tvec (x := x) (bb i) = v' i := fun i => (tcoord_spec hx _ _).symm
  have hmem : ∀ c, c ∈ eigLat hx act' (fun a => τ a) ↔ ∀ a, tvec (x := x) c ≫ act' a = spMap (scaleD (τ a)) ≫ tvec (x := x) c := by
    intro c
    rw [mem_eigLat_iff]
    exact forall_congr' fun a => (tvec_eig_iff hx (act' a) c (τ a)).symm
  have hbW : ∀ i, bb i ∈ eigLat hx act' (fun a => τ a) := fun i => (hmem _).mpr fun a => by
    rw [htv]
    exact (hv'e i).2 a
  let P : (Fin N → k) → (sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G) :=
    fun d => (List.ofFn fun i => spMap (scaleD (d i)) ≫ v' i).prod
  let Wd : (Fin N → k) → (viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G') :=
    fun d => (List.ofFn fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i).prod
  have hPW : ∀ d, Rel (F := F) tk g (Wd d) (P d) := fun d => rel_prod hc hg _ _ fun i => rel_pre _ (hv' i)
  have hPeq : ∀ d, P d = tvec (x := x) (∑ i, d i • bb i) := by
    intro d
    obtain ⟨h, e⟩ := list_prod_tan' hx (fun i => spMap (scaleD (d i)) ≫ v' i) (fun i => isTan_scale (d i) (hv'e i).1)
    refine (tcoord_spec hx (P d) h).trans ?_
    show tvec (x := x) (tcoord hx (P d) h) = _
    rw [e]
    congr 1
    exact Finset.sum_congr rfl fun i _ => tcoord_scale hx (d i) (hv'e i).1
  have hsum : ∀ d : Fin N → k, (∑ i, d i • bb i) ∈ eigLat hx act' (fun a => τ a) := fun d =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hbW i)
  have hWeig : ∀ d : Fin N → k, Geo.Tor.IsLieEigen act tk τ (Wd d) := fun d => (hT _ _ (hPW d)).mpr
    ⟨by rw [hPeq]; exact isTan_tvec hx _, by rw [hPeq]; exact (hmem _).mp (hsum d)⟩
  have hsat : ∀ d : Fin N → k, ∃ u : Fin N → (Geo.Tor.epsPt tk ⟶ G'),
      (∀ i, (u i).left = Geo.Tor.spMap (Geo.Tor.epsScale (d i)) ≫ (vB i).left) ∧ Wd d = (List.ofFn u).prod :=
    fun d => ⟨fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i, fun i => rfl, rfl⟩
  have hli : LinearIndependent k bb := by
    rw [Fintype.linearIndependent_iff]
    intro d hd
    have e1 : P d = P 0 := by
      rw [hPeq, hPeq, hd]
      simp
    have e2 : Wd d = Wd 0 := (rel_eq_iff hc (hPW d) (hPW 0)).mpr e1
    have := (huq (Wd 0) (hWeig 0)).unique (e2 ▸ hsat d) (hsat 0)
    exact fun i => congrFun this i
  have hspan : eigLat hx act' (fun a => τ a) = Submodule.span k (Set.range bb) := by
    apply le_antisymm
    · intro c hc'
      obtain ⟨w, hw⟩ := rel_exists_w hc hg (tvec (x := x) c)
      obtain ⟨d, ⟨u, hu, hwu⟩, -⟩ := huq w ((hT _ _ hw).mpr ⟨isTan_tvec hx c, (hmem c).mp hc'⟩)
      have hu' : u = fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i :=
        funext fun i => Over.OverMorphism.ext (hu i)
      have e1 : w = Wd d := by rw [hwu, hu']
      have e2 : tvec (x := x) c = P d := rel_uniq_v (e1 ▸ hw) (hPW d)
      rw [hPeq] at e2
      rw [tvec_inj hx e2]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hbW i
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]
end ReciprocityTheory.ChartRestriction.G.Chart
