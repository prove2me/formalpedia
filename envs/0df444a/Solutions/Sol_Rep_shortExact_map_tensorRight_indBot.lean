-- Prove2me | solution 1 for Rep.shortExact_map_tensorRight_indBot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c0e90084-d044-5218-a9f9-2a4f3011d821

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_shortExact_map_tensorRight_indBot

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

namespace P2mS26F12
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

end model

variable [DecidableEq G]

def e (B : Rep.{u} k G) : (B.indBot : Type u) ≃ₗ[k] ((G →₀ k) ⊗[k] B) :=
  (E (G := G) (Rep.res (⊥ : Subgroup G).subtype B).ρ).symm.trans (finsuppScalarLeft k B G).symm

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

def eR (P B : Rep.{u} k G) : ((P ⊗ B.indBot : Rep.{u} k G) : Type u) ≃ₗ[k] ((G →₀ k) ⊗[k] ((P ⊗ B : Rep.{u} k G) : Type u)) :=
  (TensorProduct.congr (LinearEquiv.refl k P) (e B)).trans (TensorProduct.leftComm k P (G →₀ k) B)

lemma eR_tmul (P B : Rep.{u} k G) (x : P) (w : B.indBot) :
    eR P B (x ⊗ₜ[k] w) = TensorProduct.leftComm k P (G →₀ k) B (x ⊗ₜ[k] e B w) := rfl

lemma eR_square {P Q : Rep.{u} k G} (φ : P ⟶ Q) (B : Rep.{u} k G) :
    LinearMap.lTensor (G →₀ k) (LinearMap.rTensor B φ.hom.toLinearMap) ∘ₗ (eR P B).toLinearMap
      = (eR Q B).toLinearMap ∘ₗ LinearMap.rTensor B.indBot φ.hom.toLinearMap := by
  refine TensorProduct.ext' fun x w => ?_
  change LinearMap.lTensor (G →₀ k) (LinearMap.rTensor B φ.hom.toLinearMap) (eR P B (x ⊗ₜ[k] w))
    = eR Q B (φ.hom.toLinearMap x ⊗ₜ[k] w)
  rw [eR_tmul, eR_tmul]
  induction e B w using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => rw [TensorProduct.tmul_add, map_add, map_add, hs, ht, TensorProduct.tmul_add, map_add]
  | tmul c b =>
    rw [TensorProduct.leftComm_tmul, TensorProduct.leftComm_tmul, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul]

end

end P2mS26F12

open P2mS26F12 in
theorem solution {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (B : Rep.{u} k G) (hXB : (X.map (MonoidalCategory.tensorRight B)).ShortExact) :
    (X.map (MonoidalCategory.tensorRight B.indBot)).ShortExact := by
  classical
  obtain ⟨hfg, hf, hg⟩ := exact_of_shortExact hXB
  have ef : (X.map (MonoidalCategory.tensorRight B)).f.hom.toLinearMap = LinearMap.rTensor B X.f.hom.toLinearMap := by
    change (X.f ▷ B).hom.toLinearMap = _
    rw [Rep.hom_whiskerRight, Representation.IntertwiningMap.toLinearMap_rTensor]
  have eg : (X.map (MonoidalCategory.tensorRight B)).g.hom.toLinearMap = LinearMap.rTensor B X.g.hom.toLinearMap := by
    change (X.g ▷ B).hom.toLinearMap = _
    rw [Rep.hom_whiskerRight, Representation.IntertwiningMap.toLinearMap_rTensor]
  rw [ef] at hfg hf
  rw [eg] at hfg hg
  refine shortExact_of_ladder (G →₀ k) hfg hf hg (eR X.X₁ B) (eR X.X₂ B) (eR X.X₃ B) ?_ ?_
  · refine (eR_square X.f B).trans ?_
    change _ = _ ∘ₗ (X.f ▷ B.indBot).hom.toLinearMap
    rw [Rep.hom_whiskerRight, Representation.IntertwiningMap.toLinearMap_rTensor]
  · refine (eR_square X.g B).trans ?_
    change _ = _ ∘ₗ (X.g ▷ B.indBot).hom.toLinearMap
    rw [Rep.hom_whiskerRight, Representation.IntertwiningMap.toLinearMap_rTensor]

end S_Rep_shortExact_map_tensorRight_indBot
end P2MW
export P2MW.S_Rep_shortExact_map_tensorRight_indBot (solution)
