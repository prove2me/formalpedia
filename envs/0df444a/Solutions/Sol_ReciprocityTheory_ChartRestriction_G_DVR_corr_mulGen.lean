-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.corr_mulGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:45.682039+00:00
-- url     : https://prove2.me/submissions/082f085c-e6b3-4a52-af4b-efb7e7f6a4df

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' K₂ K₂' : Type} [Fintype K] [Fintype K'] [Fintype K₂] [Fintype K₂']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
  {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {φ₂' : K₂' → (Y ⟶ X)} {ε₂' : K₂' → ℤ}
private lemma res_res_lemma {A : Scheme.{0}} {U V W : A.Opens} (h1 : V ≤ U) (h2 : W ≤ V)
    (a : Γ(A, U)ˣ) : res h2 (res h1 a) = res (h2.trans h1) a := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  try rfl
private lemma res_eq_res_of_le_of_res_eq {A : Scheme.{0}} {U V V0 O : A.Opens} {a : Γ(A, U)ˣ} {b : Γ(A, V)ˣ}
    {p : V0 ≤ U} {q : V0 ≤ V} (h : res p a = res q b) (hO : O ≤ V0) (r : O ≤ U) (s : O ≤ V) :
    res r a = res s b := by
  have h' := congrArg (res hO) h
  rwa [res_res_lemma, res_res_lemma] at h'
private lemma wchart_sumElim_inf_le_wchart_inl_inf (j : K ⊕ K₂ → L.ι) (j' : K' ⊕ K₂' → L.ι) :
    LB.wchart L (Sum.elim φ φ₂) j ⊓ LB.wchart L (Sum.elim φ' φ₂') j' ≤
      LB.wchart L φ (j ∘ Sum.inl) ⊓ LB.wchart L φ' (j' ∘ Sum.inl) := fun _ hx =>
  ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.1 (Sum.inl k),
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.2 (Sum.inl k)⟩
private lemma wchart_sumElim_inf_le_wchart_inr_inf (j : K ⊕ K₂ → L.ι) (j' : K' ⊕ K₂' → L.ι) :
    LB.wchart L (Sum.elim φ φ₂) j ⊓ LB.wchart L (Sum.elim φ' φ₂') j' ≤
      LB.wchart L φ₂ (j ∘ Sum.inr) ⊓ LB.wchart L φ₂' (j' ∘ Sum.inr) := fun _ hx =>
  ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.1 (Sum.inr k),
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.2 (Sum.inr k)⟩
end ReciprocityTheory.ChartRestriction.G.DVR
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' K₂ K₂' : Type} [Fintype K] [Fintype K'] [Fintype K₂] [Fintype K₂']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
  {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {φ₂' : K₂' → (Y ⟶ X)} {ε₂' : K₂' → ℤ}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    {t₂ : LB.Gen (LB.LinComb L φ₂ ε₂)} {t₂' : LB.Gen (LB.LinComb L φ₂' ε₂')}
    (h : LB.Gen.Corr L φ ε φ' ε' t t') (h₂ : LB.Gen.Corr L φ₂ ε₂ φ₂' ε₂' t₂ t₂') :
    LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ t t₂) (LB.mulGen L _ _ _ _ t' t₂') := by
  intro j j' hc hc' hk
  have e1 := h (j ∘ Sum.inl) (j' ∘ Sum.inl) (fun a b e => hc (Sum.inl a) (Sum.inl b) e)
    (fun a b e => hc' (Sum.inl a) (Sum.inl b) e) fun k k' e => hk (Sum.inl k) (Sum.inl k') e
  have e2 := h₂ (j ∘ Sum.inr) (j' ∘ Sum.inr) (fun a b e => hc (Sum.inr a) (Sum.inr b) e)
    (fun a b e => hc' (Sum.inr a) (Sum.inr b) e) fun k k' e => hk (Sum.inr k) (Sum.inr k') e
  refine (map_mul _ _ _).trans (Eq.trans ?_ (map_mul _ _ _).symm)
  refine congrArg₂ (· * ·) ?_ ?_
  · exact (res_res_lemma _ _ _).trans ((res_eq_res_of_le_of_res_eq e1 (wchart_sumElim_inf_le_wchart_inl_inf j j') _ _).trans
      (res_res_lemma _ _ _).symm)
  · exact (res_res_lemma _ _ _).trans ((res_eq_res_of_le_of_res_eq e2 (wchart_sumElim_inf_le_wchart_inr_inf j j') _ _).trans
      (res_res_lemma _ _ _).symm)
end ReciprocityTheory.ChartRestriction.G.DVR
