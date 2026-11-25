-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.cross_to_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:03:20.721554+00:00
-- url     : https://prove2.me/submissions/db2fd352-ce3e-4a06-8a17-61cc8aa5efdd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpandsAtScale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_scal_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sec_eq_of_coh
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_scal_unit_K
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_shape_cross
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {G : Over (Spec (CommRingCat.of V))}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (LG : LB G.left) (hLG : LG.IsLB) (f : G ⟶ G) (k m : ℕ)
    (σ : Fin 2 → LB.Sec (LB.LinComb LG (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (m : ℤ))))
    (τ : Fin 2 → LB.Sec (LB.LinComb LG (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (s'' : Fin 2 → LB.Sec (LB.LinComb LG (K := Fin 1) (fun _ => pullback.fst G.hom (jK V)) (fun _ => (m : ℤ))))
    (s : Fin 2 → LB.Sec (LB.LinComb LG (K := Fin 1) (fun _ => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ))))
    (lam : Fin 2 → V) (hlam : ∀ i, lam i ≠ 0)
    (hσ : ∀ i, GeneratorPullback.SecScal LG (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => (m : ℤ)) (s'' i)
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (m : ℤ)) (σ i) (pullback.fst G.hom (jK V))
      (scal (pullback.snd G.hom (jK V) ≫ jK V) (lam i)))
    (hτ : ∀ i, GeneratorPullback.SecScal LG (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)) (s i)
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) (τ i) (pullback.fst G.hom (jK V))
      (scal (pullback.snd G.hom (jK V) ≫ jK V) (lam i)))
    (hC : ∀ j, (mulSec LG _ _ _ _ (σ 0) (pullSec LG _ _ (τ 1) f.left)).f j =
      (mulSec LG _ _ _ _ (σ 1) (pullSec LG _ _ (τ 0) f.left)).f j) :
    ∀ j, (mulSec LG _ _ _ _ (s'' 0) (pullSec LG _ _ (s 1) (endK f))).f j =
      (mulSec LG _ _ _ _ (s'' 1) (pullSec LG _ _ (s 0) (endK f))).f j := by
  apply sec_eq_of_coh hLG
  intro J _
  have he : endK f ≫ pullback.fst G.hom (jK V) = pullback.fst G.hom (jK V) ≫ f.left := by
    unfold endK
    exact pullback.lift_fst _ _ _
  have hce : ∀ i, (endK f).appTop.hom (scal (pullback.snd G.hom (jK V) ≫ jK V) (lam i)) =
      scal (pullback.snd G.hom (jK V) ≫ jK V) (lam i) := fun i =>
    scal_pull (endK f) _ _ (by unfold endK; rw [← Category.assoc, pullback.lift_snd, Category.comp_id]) (lam i)
  have hCJ := hC J
  simp only [mulSec, pullSec] at hCJ ⊢
  erw [rs_rs, rs_rs] at hCJ
  erw [rs_rs, rs_rs]
  have hbase : ∀ p, (endK f ≫ pullback.fst G.hom (jK V)).base p = (pullback.fst G.hom (jK V) ≫ f.left).base p :=
    fun p => by rw [he]
  have mW : ∀ p ∈ LB.wchart LG (Sum.elim (fun _ : Fin 1 => pullback.fst G.hom (jK V))
      (fun _ : Fin 1 => endK f ≫ pullback.fst G.hom (jK V))) J,
      (pullback.fst G.hom (jK V)).base p ∈ LG.U (J (Sum.inl 0)) ∧
      (pullback.fst G.hom (jK V) ≫ f.left).base p ∈ LG.U (J (Sum.inr 0)) := fun p hp =>
    ⟨Set.mem_iInter.1 hp (Sum.inl 0), hbase p ▸ Set.mem_iInter.1 hp (Sum.inr 0)⟩
  have f1 : ∀ (q : Fin 1), q = 0 := fun q => Subsingleton.elim _ _
  have key := shape_cross (pullback.fst G.hom (jK V)) (endK f) f.left he
    (fun i => scal (pullback.snd G.hom (jK V) ≫ jK V) (lam i)) hce
    (Ua := LB.wchart LG (fun _ : Fin 1 => 𝟙 G.left) (J ∘ Sum.inl))
    (Ub := LB.wchart LG (fun _ : Fin 1 => 𝟙 G.left) (J ∘ Sum.inr))
    (O := LB.wchart LG (Sum.elim (fun _ : Fin 1 => 𝟙 G.left) (fun _ : Fin 1 => f.left ≫ 𝟙 G.left)) J)
    (Sa := LB.wchart LG (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (J ∘ Sum.inl))
    (Sb := LB.wchart LG (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (J ∘ Sum.inr))
    (Wa := LB.wchart LG (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (J ∘ Sum.inl) ⊓
      LB.wchart LG (fun _ : Fin 1 => pullback.fst G.hom (jK V) ≫ 𝟙 G.left) (J ∘ Sum.inl))
    (Wb := LB.wchart LG (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (J ∘ Sum.inr) ⊓
      LB.wchart LG (fun _ : Fin 1 => pullback.fst G.hom (jK V) ≫ 𝟙 G.left) (J ∘ Sum.inr))
    (W := LB.wchart LG (Sum.elim (fun _ : Fin 1 => pullback.fst G.hom (jK V))
      (fun _ : Fin 1 => endK f ≫ pullback.fst G.hom (jK V))) J)
    _ _ _ _ _ _
    (fun p hp => Set.mem_iInter.2 fun q => by
      rcases q with q | q <;> rw [f1 q]
      · exact (mW p hp).1
      · exact (mW p hp).2)
    (fun p hp => ⟨Set.mem_iInter.2 fun q => by rw [f1 q]; exact (mW p hp).1,
      Set.mem_iInter.2 fun q => by rw [f1 q]; exact (mW p hp).1⟩)
    (fun p hp => Set.mem_iInter.2 fun q => by rw [f1 q]; exact (mW p hp).1)
    (fun p hp => ⟨Set.mem_iInter.2 fun q => by rw [f1 q]; exact Set.mem_iInter.1 hp (Sum.inr 0),
      Set.mem_iInter.2 fun q => by rw [f1 q]; exact Set.mem_iInter.1 hp (Sum.inr 0)⟩)
    (fun p hp => Set.mem_iInter.2 fun q => by rw [f1 q]; exact Set.mem_iInter.1 hp (Sum.inr 0))
    (fun i => scal_unit_K (lam i) (hlam i))
    (fun i => (σ i).f (J ∘ Sum.inl)) (fun i => (τ i).f (J ∘ Sum.inr))
    (fun i => (s'' i).f (J ∘ Sum.inl)) (fun i => (s i).f (J ∘ Sum.inr)) hCJ
    (fun i => hσ i _ _ (fun k₁ k₂ _ => by rcases k₁ with k₁ | k₁ <;> rcases k₂ with k₂ | k₂ <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> congr 1 <;> exact Subsingleton.elim _ _))
    (fun i => hτ i _ _ (fun k₁ k₂ _ => by rcases k₁ with k₁ | k₁ <;> rcases k₂ with k₂ | k₂ <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> congr 1 <;> exact Subsingleton.elim _ _))
  exact key
end ReciprocityTheory.ChartRestriction.G.DVR
