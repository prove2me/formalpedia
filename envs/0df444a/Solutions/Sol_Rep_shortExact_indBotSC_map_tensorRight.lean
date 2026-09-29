-- Prove2me | solution 1 for Rep.shortExact_indBotSC_map_tensorRight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/3d6a0219-3a25-5935-b8b2-beacc5ec217a

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_GroupCohomology_TateDimensionShiftMaps
import Theorems.Thm_Rep_indBotMap_indBotMk
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_shortExact_indBotSC_map_tensorRight

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

namespace P2mS26W14d8
p2m_open "Representation TensorProduct Representation.TensorProduct"

noncomputable section

variable {k G : Type u} [CommRing k] [Group G]

section model
variable {W : Type u} [AddCommGroup W] [Module k W] (ρ : Representation k (⊥ : Subgroup G) W)

lemma ker_tprod_bot_eq_bot :
    Representation.Coinvariants.ker (V := MonoidAlgebra k G ⊗[k] W)
      (Representation.tprod ((Representation.leftRegular k G).comp (⊥ : Subgroup G).subtype) ρ) = ⊥ := by
  rw [Representation.Coinvariants.ker, Submodule.span_eq_bot]
  rintro _ ⟨⟨g, v⟩, rfl⟩
  have hg : g = 1 := Subsingleton.elim _ _
  simp [hg]

def E [DecidableEq G] : (G →₀ W) ≃ₗ[k] Representation.IndV (⊥ : Subgroup G).subtype ρ :=
  (finsuppScalarLeft k W G).symm.trans <|
    (TensorProduct.congr (MonoidAlgebra.coeffLinearEquiv k).symm (LinearEquiv.refl k W)).trans
      ((Submodule.quotEquivOfEqBot _ (ker_tprod_bot_eq_bot ρ)).symm :
        (MonoidAlgebra k G ⊗[k] W) ≃ₗ[k] Representation.Coinvariants (V := MonoidAlgebra k G ⊗[k] W)
          (Representation.tprod ((Representation.leftRegular k G).comp (⊥ : Subgroup G).subtype) ρ))

lemma E_single [DecidableEq G] (g : G) (w : W) :
    E ρ (Finsupp.single g w) = Representation.IndV.mk (⊥ : Subgroup G).subtype ρ g w := by
  rw [E, LinearEquiv.trans_apply, finsuppScalarLeft_symm_apply_single, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul]
  rfl

end model

variable [DecidableEq G]

def e (A : Rep.{u} k G) : (A.indBot : Type u) ≃ₗ[k] ((G →₀ k) ⊗[k] A) :=
  (E (G := G) (Rep.res (⊥ : Subgroup G).subtype A).ρ).symm.trans (finsuppScalarLeft k A G).symm

lemma e_indBotMk (A : Rep.{u} k G) (g : G) (a : A) : e A (A.indBotMk g a) = Finsupp.single g (1 : k) ⊗ₜ[k] a := by
  have h : E (G := G) (Rep.res (⊥ : Subgroup G).subtype A).ρ (Finsupp.single g a) = A.indBotMk g a := by
    rw [E_single]; rfl
  rw [e, LinearEquiv.trans_apply, show (E (G := G) (Rep.res (⊥ : Subgroup G).subtype A).ρ).symm (A.indBotMk g a)
    = Finsupp.single g a from (LinearEquiv.symm_apply_eq _).2 h.symm, finsuppScalarLeft_symm_apply_single]

lemma indBot_induction (A : Rep.{u} k G) {P : A.indBot → Prop} (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hmk : ∀ (g : G) (a : A), P (A.indBotMk g a)) (x : A.indBot) : P x := by
  obtain ⟨f, rfl⟩ := (E (G := G) (Rep.res (⊥ : Subgroup G).subtype A).ρ).surjective x
  induction f using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact h0
  | add f f' hf hf' => rw [map_add]; exact hadd _ _ hf hf'
  | single g a => rw [E_single]; exact hmk g a

lemma e_square {A B : Rep.{u} k G} (φ : A ⟶ B) :
    LinearMap.lTensor (G →₀ k) φ.hom.toLinearMap ∘ₗ (e A).toLinearMap = (e B).toLinearMap ∘ₗ (Rep.indBotMap φ).hom.toLinearMap := by
  refine LinearMap.ext fun x => ?_
  induction x using indBot_induction A with
  | h0 => simp
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]
  | hmk g a =>
    change LinearMap.lTensor (G →₀ k) φ.hom.toLinearMap (e A (A.indBotMk g a)) = e B ((Rep.indBotMap φ).hom (A.indBotMk g a))
    rw [e_indBotMk, LinearMap.lTensor_tmul, Rep.indBotMap_indBotMk, e_indBotMk]
    rfl

omit [DecidableEq G] in

lemma exact_of_shortExact {T : ShortComplex (Rep.{u} k G)} (hT : T.ShortExact) :
    Function.Exact T.f.hom.toLinearMap T.g.hom.toLinearMap ∧ Function.Injective T.f.hom.toLinearMap
      ∧ Function.Surjective T.g.hom.toLinearMap :=
  ⟨LinearMap.exact_iff.2 ((hT.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker).symm,
    (Rep.mono_iff_injective T.f).1 hT.mono_f, (Rep.epi_iff_surjective T.g).1 hT.epi_g⟩

omit [DecidableEq G] in

theorem shortExact_of_ladder (F : Type u) [AddCommGroup F] [Module k F] [Module.Flat k F]
    {S : ShortComplex (Rep.{u} k G)} {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂]
    [AddCommGroup M₃] [Module k M₃] {f : M₁ →ₗ[k] M₂} {g : M₂ →ₗ[k] M₃}
    (hfg : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g)
    (e₁ : S.X₁ ≃ₗ[k] F ⊗[k] M₁) (e₂ : S.X₂ ≃ₗ[k] F ⊗[k] M₂) (e₃ : S.X₃ ≃ₗ[k] F ⊗[k] M₃)
    (h₁₂ : LinearMap.lTensor F f ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ S.f.hom.toLinearMap)
    (h₂₃ : LinearMap.lTensor F g ∘ₗ e₂.toLinearMap = e₃.toLinearMap ∘ₗ S.g.hom.toLinearMap) :
    S.ShortExact := by
  have ex : Function.Exact (LinearMap.lTensor F f) (LinearMap.lTensor F g) := lTensor_exact F hfg hg
  have exS : Function.Exact S.f.hom.toLinearMap S.g.hom.toLinearMap :=
    (Function.Exact.iff_of_ladder_linearEquiv h₁₂ h₂₃).1 ex
  have inj : Function.Injective S.f.hom.toLinearMap := by
    have h : Function.Injective (e₂.toLinearMap ∘ₗ S.f.hom.toLinearMap) := by
      rw [← h₁₂]
      exact (Module.Flat.lTensor_preserves_injective_linearMap f hf).comp e₁.injective
    exact Function.Injective.of_comp h
  have surj : Function.Surjective S.g.hom.toLinearMap := by
    have h : Function.Surjective (e₃.toLinearMap ∘ₗ S.g.hom.toLinearMap) := by
      rw [← h₂₃]
      exact (LinearMap.lTensor_surjective F hg).comp e₂.surjective
    intro y
    obtain ⟨x, hx⟩ := h (e₃ y)
    exact ⟨x, e₃.injective hx⟩
  exact
    { exact := by
        refine (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful _ ((ShortComplex.moduleCat_exact_iff _).2 ?_)
        intro y hy
        exact (exS y).1 hy
      mono_f := (Rep.mono_iff_injective _).2 inj
      epi_g := (Rep.epi_iff_surjective _).2 surj }

end

end P2mS26W14d8

namespace P2mS26W14d8
open TensorProduct
variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]

noncomputable def e8 (A B : Rep.{u} k G) : ((A.indBot ⊗ B : Rep.{u} k G) : Type u) ≃ₗ[k] ((G →₀ k) ⊗[k] (A ⊗ B : Rep.{u} k G)) :=
  (TensorProduct.congr (e A) (LinearEquiv.refl k B)).trans (TensorProduct.assoc k (G →₀ k) A B)

lemma e8_tmul (A B : Rep.{u} k G) (g : G) (a : A) (b : B) :
    e8 A B (A.indBotMk g a ⊗ₜ[k] b) = Finsupp.single g (1 : k) ⊗ₜ[k] (a ⊗ₜ[k] b) := by
  change TensorProduct.assoc k (G →₀ k) A B (TensorProduct.congr (e A) (LinearEquiv.refl k B) (A.indBotMk g a ⊗ₜ[k] b)) = _
  rw [TensorProduct.congr_tmul, e_indBotMk, LinearEquiv.refl_apply, TensorProduct.assoc_tmul]

lemma e8_square {A A' : Rep.{u} k G} (φ : A ⟶ A') (B : Rep.{u} k G) :
    LinearMap.lTensor (G →₀ k) (φ ▷ B).hom.toLinearMap ∘ₗ (e8 A B).toLinearMap
      = (e8 A' B).toLinearMap ∘ₗ (Rep.indBotMap φ ▷ B).hom.toLinearMap := by
  refine TensorProduct.ext' fun x b => ?_
  induction x using indBot_induction A with
  | h0 => simp
  | hadd x y hx hy => rw [TensorProduct.add_tmul, map_add, map_add, hx, hy]
  | hmk g a =>
    change LinearMap.lTensor (G →₀ k) (φ ▷ B).hom.toLinearMap (e8 A B (A.indBotMk g a ⊗ₜ[k] b))
      = e8 A' B ((Rep.indBotMap φ).hom (A.indBotMk g a) ⊗ₜ[k] b)
    rw [e8_tmul, LinearMap.lTensor_tmul, Rep.indBotMap_indBotMk, e8_tmul]
    rfl

end P2mS26W14d8

open P2mS26W14d8 in
theorem solution {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (B : Rep.{u} k G) (hXB : (X.map (MonoidalCategory.tensorRight B)).ShortExact) :
    ((Rep.indBotSC X).map (MonoidalCategory.tensorRight B)).ShortExact := by
  classical
  obtain ⟨hfg, hf, hg⟩ := exact_of_shortExact hXB
  exact shortExact_of_ladder (G →₀ k) hfg hf hg (e8 X.X₁ B) (e8 X.X₂ B) (e8 X.X₃ B) (e8_square X.f B) (e8_square X.g B)

end S_Rep_shortExact_indBotSC_map_tensorRight
end P2MW
export P2MW.S_Rep_shortExact_indBotSC_map_tensorRight (solution)
