-- Prove2me | solution 1 for Rep.shortExact_dimShiftDownSC_map_tensorRight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/9b714d23-97fa-5aa4-ab65-b367c7db8f64

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_GroupCohomology_TateDimensionShiftMaps
import Theorems.Thm_Rep_indBotMap_indBotMk
import Theorems.Thm_Rep_indBotPi_indBotSigma
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_shortExact_dimShiftDownSC_map_tensorRight

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

namespace P2mS26W14d10
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

end P2mS26W14d10

namespace P2mS26W14d10
p2m_open "Representation TensorProduct Representation.TensorProduct"

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]

abbrev Gne : Set G := {g | g ≠ 1}

abbrev EA (A : Rep.{u} k G) : (G →₀ A) ≃ₗ[k] (A.indBot : Type u) := E (G := G) (Rep.res (⊥ : Subgroup G).subtype A).ρ

lemma EA_single (A : Rep.{u} k G) (g : G) (a : A) : EA A (Finsupp.single g a) = A.indBotMk g a := by
  rw [EA, E_single]; rfl

abbrev MR {A B : Rep.{u} k G} (φ : A ⟶ B) : (G →₀ A) →ₗ[k] (G →₀ B) := Finsupp.mapRange.linearMap φ.hom.toLinearMap

lemma indBotMap_EA {A B : Rep.{u} k G} (φ : A ⟶ B) (f : G →₀ A) :
    (Rep.indBotMap φ).hom (EA A f) = EA B (MR φ f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => rw [map_add, map_add, map_add, map_add, hf, hf']
  | single g a =>
    rw [EA_single, Rep.indBotMap_indBotMk, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, EA_single]
    rfl

lemma EA_symm_indBotMap {A B : Rep.{u} k G} (φ : A ⟶ B) (y : A.indBot) :
    (EA B).symm ((Rep.indBotMap φ).hom y) = MR φ ((EA A).symm y) := by
  obtain ⟨f, rfl⟩ := (EA A).surjective y
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_eq, indBotMap_EA]

def Θ (A : Rep.{u} k G) : (A.dimShiftDownObj : Type u) →ₗ[k] (↥(Gne (G := G)) →₀ A) :=
  Finsupp.lsubtypeDomain (Gne (G := G)) ∘ₗ (EA A).symm.toLinearMap
    ∘ₗ (LinearMap.ker (Rep.indBotπ A).hom.toLinearMap).subtype

lemma Θ_apply (A : Rep.{u} k G) (x : A.dimShiftDownObj) (g : ↥(Gne (G := G))) :
    Θ A x g = (EA A).symm (x : A.indBot) (g : G) := rfl

lemma Θ_injective (A : Rep.{u} k G) : Function.Injective (Θ A) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  set f := (EA A).symm (x : A.indBot) with hf
  have hfg : ∀ g : G, g ≠ 1 → f g = 0 := fun g hg => by
    have := DFunLike.congr_fun hx ⟨g, hg⟩
    rwa [Θ_apply, Finsupp.zero_apply] at this
  have hf1 : f = Finsupp.single 1 (f 1) := Finsupp.ext fun g => by
    by_cases h : g = 1
    · subst h; rw [Finsupp.single_eq_same]
    · rw [Finsupp.single_apply, if_neg (Ne.symm h), hfg g h]
  have hx1 : (x : A.indBot) = A.indBotσ (f 1) := by
    rw [show (x : A.indBot) = EA A f from ((EA A).apply_symm_apply _).symm, hf1, EA_single, Finsupp.single_eq_same]
    rfl
  have hπ : (Rep.indBotπ A).hom (x : A.indBot) = 0 := x.2
  rw [hx1, Rep.indBotPi_indBotSigma] at hπ
  apply Subtype.ext
  rw [hx1, hπ, map_zero]
  rfl

lemma Θ_surjective (A : Rep.{u} k G) : Function.Surjective (Θ A) := by
  intro h
  let f₀ : G →₀ A := h.extendDomain
  let x₀ : A.indBot := EA A f₀
  let c : A := (Rep.indBotπ A).hom x₀
  have hx₁ : x₀ - A.indBotσ c ∈ LinearMap.ker (Rep.indBotπ A).hom.toLinearMap := by
    rw [LinearMap.mem_ker, map_sub, Representation.IntertwiningMap.toLinearMap_apply,
      Representation.IntertwiningMap.toLinearMap_apply, Rep.indBotPi_indBotSigma, sub_self]
  refine ⟨⟨x₀ - A.indBotσ c, hx₁⟩, Finsupp.ext fun g => ?_⟩
  obtain ⟨g, hg⟩ := g
  rw [Θ_apply]
  change (EA A).symm (EA A f₀ - A.indBotσ c) g = h ⟨g, hg⟩
  have hσ : A.indBotσ c = EA A (Finsupp.single 1 c) := by rw [EA_single]; rfl
  rw [hσ, ← map_sub, LinearEquiv.symm_apply_apply, Finsupp.sub_apply, Finsupp.single_apply,
    if_neg (Ne.symm (show g ≠ 1 from hg)), sub_zero, Finsupp.extendDomain_apply, dif_pos hg]

def e7 (A : Rep.{u} k G) : (A.dimShiftDownObj : Type u) ≃ₗ[k] ((↥(Gne (G := G)) →₀ k) ⊗[k] A) :=
  (LinearEquiv.ofBijective (Θ A) ⟨Θ_injective A, Θ_surjective A⟩).trans (finsuppScalarLeft k A _).symm

lemma e7_apply (A : Rep.{u} k G) (x : A.dimShiftDownObj) : e7 A x = (finsuppScalarLeft k A _).symm (Θ A x) := rfl

lemma Θ_natural {A B : Rep.{u} k G} (φ : A ⟶ B) (x : A.dimShiftDownObj) :
    Θ B ((Rep.dimShiftDownObjMap φ).hom x) = Finsupp.mapRange.linearMap φ.hom.toLinearMap (Θ A x) := by
  refine Finsupp.ext fun g => ?_
  rw [Θ_apply, Rep.coe_dimShiftDownObjMap_apply, EA_symm_indBotMap, Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, Θ_apply]

lemma fSL_symm_mapRange {A B : Rep.{u} k G} (φ : A ⟶ B) (h : ↥(Gne (G := G)) →₀ A) :
    (finsuppScalarLeft k B _).symm (Finsupp.mapRange.linearMap φ.hom.toLinearMap h)
      = LinearMap.lTensor _ φ.hom.toLinearMap ((finsuppScalarLeft k A _).symm h) := by
  induction h using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add f f' hf hf' => rw [map_add, map_add, map_add, map_add, hf, hf']
  | single i a =>
    rw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, finsuppScalarLeft_symm_apply_single,
      finsuppScalarLeft_symm_apply_single, LinearMap.lTensor_tmul]

lemma e7_square {A B : Rep.{u} k G} (φ : A ⟶ B) :
    LinearMap.lTensor _ φ.hom.toLinearMap ∘ₗ (e7 A).toLinearMap = (e7 B).toLinearMap ∘ₗ (Rep.dimShiftDownObjMap φ).hom.toLinearMap := by
  refine LinearMap.ext fun x => ?_
  change LinearMap.lTensor _ φ.hom.toLinearMap (e7 A x) = e7 B ((Rep.dimShiftDownObjMap φ).hom x)
  rw [e7_apply, e7_apply, Θ_natural, fSL_symm_mapRange]

end

end P2mS26W14d10

namespace P2mS26W14d10
open TensorProduct
variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]

noncomputable def e10 (A B : Rep.{u} k G) :
    ((A.dimShiftDownObj ⊗ B : Rep.{u} k G) : Type u) ≃ₗ[k] ((↥(Gne (G := G)) →₀ k) ⊗[k] (A ⊗ B : Rep.{u} k G)) :=
  (TensorProduct.congr (e7 A) (LinearEquiv.refl k B)).trans (TensorProduct.assoc k _ A B)

lemma e10_square {A A' : Rep.{u} k G} (φ : A ⟶ A') (B : Rep.{u} k G) :
    LinearMap.lTensor _ (φ ▷ B).hom.toLinearMap ∘ₗ (e10 A B).toLinearMap
      = (e10 A' B).toLinearMap ∘ₗ (Rep.dimShiftDownObjMap φ ▷ B).hom.toLinearMap := by
  have key : ∀ (t : (↥(Gne (G := G)) →₀ k) ⊗[k] A) (b : B),
      LinearMap.lTensor _ (φ ▷ B).hom.toLinearMap (TensorProduct.assoc k _ A B (t ⊗ₜ[k] b))
        = TensorProduct.assoc k _ A' B (LinearMap.lTensor _ φ.hom.toLinearMap t ⊗ₜ[k] b) := by
    intro t b
    induction t using TensorProduct.induction_on with
    | zero => rw [TensorProduct.zero_tmul, map_zero, map_zero, map_zero, TensorProduct.zero_tmul, map_zero]
    | add t t' ht ht' => rw [TensorProduct.add_tmul, map_add, map_add, ht, ht', map_add, TensorProduct.add_tmul, map_add]
    | tmul s a => rw [TensorProduct.assoc_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.assoc_tmul]; rfl
  refine TensorProduct.ext' fun x b => ?_
  change LinearMap.lTensor _ (φ ▷ B).hom.toLinearMap (TensorProduct.assoc k _ A B
      (TensorProduct.congr (e7 A) (LinearEquiv.refl k B) (x ⊗ₜ[k] b)))
    = TensorProduct.assoc k _ A' B (TensorProduct.congr (e7 A') (LinearEquiv.refl k B)
      ((Rep.dimShiftDownObjMap φ).hom x ⊗ₜ[k] b))
  rw [TensorProduct.congr_tmul, TensorProduct.congr_tmul, LinearEquiv.refl_apply, key,
    show e7 A' ((Rep.dimShiftDownObjMap φ).hom x) = LinearMap.lTensor _ φ.hom.toLinearMap (e7 A x) from
      (LinearMap.congr_fun (e7_square φ) x).symm]

end P2mS26W14d10

open P2mS26W14d10 in
theorem solution {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (B : Rep.{u} k G)
    (hXB : (X.map (MonoidalCategory.tensorRight B)).ShortExact) :
    ((Rep.dimShiftDownSC X).map (MonoidalCategory.tensorRight B)).ShortExact := by
  classical
  obtain ⟨hfg, hf, hg⟩ := exact_of_shortExact hXB
  exact shortExact_of_ladder (↥(Gne (G := G)) →₀ k) hfg hf hg (e10 X.X₁ B) (e10 X.X₂ B) (e10 X.X₃ B)
    (e10_square X.f B) (e10_square X.g B)

end S_Rep_shortExact_dimShiftDownSC_map_tensorRight
end P2MW
export P2MW.S_Rep_shortExact_dimShiftDownSC_map_tensorRight (solution)
