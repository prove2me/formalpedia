-- Prove2me | solution 1 for Rep.nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/48fc7fac-32ab-54aa-9fca-fc73e64d6ceb

import Mathlib
import Theorems.Thm_Rep_exists_hom_injective_finiteIndex_of_finrank_invariants_eq
import Theorems.Thm_Rep_nonempty_tensor_trivial_zmod_iso_of_injective_of_finiteIndex
import Theorems.Thm_Rep_eq_of_additive_of_forall_nonempty_res_iso
import Theorems.Thm_Rep_finrank_hom_eq_add_of_shortExact_of_card_coprime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module"
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace P2mS25DecompWD

open scoped TensorProduct Pointwise

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime]

section Red

variable (p)
variable (V : Type*) [AddCommGroup V]

abbrev pSub : Submodule ℤ V := (p : ℤ) • ⊤

abbrev Red := V ⧸ pSub p V

lemma p_smul_mk (v : V) : (p : ℤ) • (Submodule.Quotient.mk v : Red p V) = 0 := by
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

lemma p_nsmul_eq_zero (x : Red p V) : p • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H v => rw [← natCast_zsmul]; exact p_smul_mk p V v

noncomputable scoped instance instModuleRed : Module (ZMod p) (Red p V) :=
  AddCommGroup.zmodModule (p_nsmul_eq_zero p V)

variable {V}
variable {W : Type*} [AddCommGroup W]

noncomputable def redMap (φ : V →ₗ[ℤ] W) : Red p V →ₗ[ZMod p] Red p W :=
  (Submodule.mapQ (pSub p V) (pSub p W) φ (by
      rintro _ ⟨v, -, rfl⟩
      show φ ((p : ℤ) • v) ∈ pSub p W
      rw [map_smul]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)).toAddMonoidHom.toZModLinearMap p

@[scoped simp] lemma redMap_mk (φ : V →ₗ[ℤ] W) (v : V) :
    redMap p φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk (φ v) := rfl

lemma redMap_id : redMap p (LinearMap.id : V →ₗ[ℤ] V) = LinearMap.id := by
  apply LinearMap.ext; intro x
  induction x using Submodule.Quotient.induction_on with
  | H v => rfl

variable {U : Type*} [AddCommGroup U]

lemma redMap_comp (φ : V →ₗ[ℤ] W) (ψ : W →ₗ[ℤ] U) : redMap p (ψ ∘ₗ φ) = redMap p ψ ∘ₗ redMap p φ := by
  apply LinearMap.ext; intro x
  induction x using Submodule.Quotient.induction_on with
  | H v => rfl

variable (V)

noncomputable def redRep (ρ : Representation ℤ G V) : Representation (ZMod p) G (Red p V) where
  toFun g := redMap p (ρ g)
  map_one' := by rw [map_one]; exact redMap_id p
  map_mul' g h := by rw [map_mul]; exact redMap_comp p (ρ h) (ρ g)

@[scoped simp] lemma redRep_apply_mk (ρ : Representation ℤ G V) (g : G) (v : V) :
    redRep p V ρ g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ g v) := rfl

end Red

section Functor

variable (p)
variable {V W U : Type*} [AddCommGroup V] [AddCommGroup W] [AddCommGroup U]

abbrev X (ρ : Representation ℤ G V) := (redRep p V ρ).asModule

noncomputable def redHom (ρ : Representation ℤ G V) (σ : Representation ℤ G W) (φ : V →ₗ[ℤ] W)
    (hφ : ∀ g v, φ (ρ g v) = σ g (φ v)) : X p ρ →ₗ[MonoidAlgebra (ZMod p) G] X p σ :=
  Representation.IntertwiningMap.equivLinearMapAsModule _ _
    ((redMap p φ).intertwiningMap_of_isIntertwiningMap (redRep p V ρ) (redRep p W σ) (fun g x => by
      induction x using Submodule.Quotient.induction_on with
      | H v => simp only [redRep_apply_mk, redMap_mk, hφ]))

@[scoped simp] lemma redHom_mk (ρ : Representation ℤ G V) (σ : Representation ℤ G W) (φ : V →ₗ[ℤ] W)
    (hφ : ∀ g v, φ (ρ g v) = σ g (φ v)) (v : V) :
    redHom p ρ σ φ hφ (Submodule.Quotient.mk v) = (Submodule.Quotient.mk (φ v) : Red p W) := rfl

lemma redHom_apply (ρ : Representation ℤ G V) (σ : Representation ℤ G W) (φ : V →ₗ[ℤ] W)
    (hφ : ∀ g v, φ (ρ g v) = σ g (φ v)) (x : X p ρ) : redHom p ρ σ φ hφ x = redMap p φ x := rfl

noncomputable def redEquiv (ρ : Representation ℤ G V) (σ : Representation ℤ G W) (e : V ≃ₗ[ℤ] W)
    (he : ∀ g v, e (ρ g v) = σ g (e v)) : X p ρ ≃ₗ[MonoidAlgebra (ZMod p) G] X p σ :=
  LinearEquiv.ofLinear (redHom p ρ σ e.toLinearMap he)
    (redHom p σ ρ e.symm.toLinearMap (fun g w => by
      apply e.injective; rw [he]; simp))
    (by
      apply LinearMap.ext; intro x
      induction x using Submodule.Quotient.induction_on with
      | H v => simp [redHom_apply])
    (by
      apply LinearMap.ext; intro x
      induction x using Submodule.Quotient.induction_on with
      | H v => simp [redHom_apply])

end Functor

section Sublattice

variable (p)
variable {V : Type*} [AddCommGroup V] (ρ : Representation ℤ G V)

noncomputable def subRep (S : Submodule ℤ V) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) : Representation ℤ G S where
  toFun g := (ρ g).restrict (fun v hv => hS g v hv)
  map_one' := by ext ⟨v, hv⟩; simp
  map_mul' g h := by ext ⟨v, hv⟩; simp

@[scoped simp] lemma subRep_apply_coe (S : Submodule ℤ V) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (g : G) (v : S) :
    ((subRep ρ S hS g v : S) : V) = ρ g v := rfl

noncomputable def incl (S T : Submodule ℤ V) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (hT : ∀ g, ∀ v ∈ T, ρ g v ∈ T)
    (hST : S ≤ T) : X p (subRep ρ S hS) →ₗ[MonoidAlgebra (ZMod p) G] X p (subRep ρ T hT) :=
  redHom p _ _ (Submodule.inclusion hST) (fun g v => rfl)

noncomputable def inclTop (S : Submodule ℤ V) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) :
    X p (subRep ρ S hS) →ₗ[MonoidAlgebra (ZMod p) G] X p ρ :=
  redHom p _ _ S.subtype (fun g v => rfl)

def divP (S : Submodule ℤ V) : Submodule ℤ V := S.comap ((p : ℤ) • LinearMap.id)

lemma mem_divP {S : Submodule ℤ V} {v : V} : v ∈ divP p S ↔ (p : ℤ) • v ∈ S := Iff.rfl

lemma le_divP (S : Submodule ℤ V) : S ≤ divP p S := fun v hv => S.smul_mem _ hv

lemma divP_stable (S : Submodule ℤ V) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) : ∀ g, ∀ v ∈ divP p S, ρ g v ∈ divP p S := by
  intro g v hv
  rw [mem_divP] at hv ⊢
  rw [← map_smul]
  exact hS g _ hv

noncomputable def mulP (S : Submodule ℤ V) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) :
    X p (subRep ρ (divP p S) (divP_stable p ρ S hS)) →ₗ[MonoidAlgebra (ZMod p) G] X p (subRep ρ S hS) :=
  redHom p _ _ (((p : ℤ) • LinearMap.id : V →ₗ[ℤ] V).restrict (fun v hv => (mem_divP p).1 hv)) (fun g v => by
    apply Subtype.ext
    simp [LinearMap.restrict_apply, map_smul])

end Sublattice

section Tensor

variable (p)
variable (V : Type*) [AddCommGroup V]

noncomputable def toRed : V ⊗[ℤ] ZMod p →ₗ[ℤ] Red p V :=
  TensorProduct.lift
    { toFun := fun v => ((LinearMap.toSpanSingleton (ZMod p) (Red p V) (Submodule.Quotient.mk v)).toAddMonoidHom).toIntLinearMap
      map_add' := fun v w => by
        apply LinearMap.ext; intro a
        simp [LinearMap.toSpanSingleton_apply, Submodule.Quotient.mk_add, smul_add]
      map_smul' := fun n v => by
        apply LinearMap.ext; intro a
        show a • (Submodule.Quotient.mk (n • v) : Red p V) = n • (a • (Submodule.Quotient.mk v : Red p V))
        rw [Submodule.Quotient.mk_smul, smul_comm] }

@[scoped simp] lemma toRed_tmul (v : V) (a : ZMod p) : toRed p V (v ⊗ₜ a) = a • (Submodule.Quotient.mk v : Red p V) := by
  simp [toRed, LinearMap.toSpanSingleton_apply]

noncomputable def ofRed : Red p V →ₗ[ℤ] V ⊗[ℤ] ZMod p :=
  (pSub p V).liftQ ((TensorProduct.mk ℤ V (ZMod p)).flip 1) (by
    rintro _ ⟨v, -, rfl⟩
    show ((p : ℤ) • v) ⊗ₜ[ℤ] (1 : ZMod p) = 0
    rw [TensorProduct.smul_tmul]
    simp)

@[scoped simp] lemma ofRed_mk (v : V) : ofRed p V (Submodule.Quotient.mk v) = v ⊗ₜ (1 : ZMod p) := rfl

lemma toRed_ofRed (x : Red p V) : toRed p V (ofRed p V x) = x := by
  induction x using Submodule.Quotient.induction_on with
  | H v => simp

lemma ofRed_toRed (x : V ⊗[ℤ] ZMod p) : ofRed p V (toRed p V x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v a =>
    rw [toRed_tmul]
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
    rw [Int.cast_smul_eq_zsmul, ← Submodule.Quotient.mk_smul, ofRed_mk, TensorProduct.smul_tmul]
    congr 1
    simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end Tensor

section Natural

variable (p)
variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

lemma toRed_natural (φ : V →ₗ[ℤ] W) (x : V ⊗[ℤ] ZMod p) :
    toRed p W (TensorProduct.map φ LinearMap.id x) = redMap p φ (toRed p V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v a => simp [map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

variable (V)

noncomputable def tensorRedEquiv : V ⊗[ℤ] ZMod p ≃ₗ[ℤ] Red p V :=
  LinearEquiv.ofLinear (toRed p V) (ofRed p V) (LinearMap.ext (toRed_ofRed p V)) (LinearMap.ext (ofRed_toRed p V))

@[scoped simp] lemma tensorRedEquiv_apply (x : V ⊗[ℤ] ZMod p) : tensorRedEquiv p V x = toRed p V x := rfl

end Natural

end P2mS25DecompWD
p2m_reactivate "P2MW.S_Rep_nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq.P2mS25DecompWD"

namespace SST

section bridge

variable (k : Type) [Field k] (G : Type) [Group G]
variable (M : Type) [AddCommGroup M] [Module k M] [Module (MonoidAlgebra k G) M]
  [IsScalarTower k (MonoidAlgebra k G) M]

noncomputable def repOfModule : Representation k G M :=
  (Module.toModuleEnd k (S := MonoidAlgebra k G) M).toMonoidHom.comp (MonoidAlgebra.of k G)

@[scoped simp] lemma repOfModule_apply (g : G) (m : M) : repOfModule k G M g m = MonoidAlgebra.of k G g • m := rfl

lemma asAlgebraHom_repOfModule : (repOfModule k G M).asAlgebraHom = Algebra.lsmul k k M := by
  apply MonoidAlgebra.algHom_ext
  intro g
  apply LinearMap.ext
  intro m
  rw [Representation.asAlgebraHom_single_one]
  rfl
  exact Subsingleton.elim _ _

lemma asAlgebraHom_repOfModule_apply (x : MonoidAlgebra k G) (m : M) :
    (repOfModule k G M).asAlgebraHom x m = x • m := by
  rw [asAlgebraHom_repOfModule]; rfl

noncomputable def asModuleEquiv' : (repOfModule k G M).asModule ≃ₗ[MonoidAlgebra k G] M :=
  { (repOfModule k G M).asModuleEquiv with
    map_smul' := fun x v => by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe, RingHom.id_apply]
      rw [Representation.asModuleEquiv_map_smul, asAlgebraHom_repOfModule_apply] }

end bridge
p2m_reactivate "P2MW.S_Rep_nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq.P2mS25DecompWD"

section homs

variable {k : Type} [Field k] {G : Type} [Group G]

noncomputable def homEquivLinearMap (A B : Rep.{0} k G) :
    (A ⟶ B) ≃ₗ[k] (A.ρ.asModule →ₗ[MonoidAlgebra k G] B.ρ.asModule) where
  toFun f := Representation.IntertwiningMap.equivLinearMapAsModule A.ρ B.ρ f.hom
  invFun φ := Rep.ofHom ((Representation.IntertwiningMap.equivLinearMapAsModule A.ρ B.ρ).symm φ)
  map_add' f g := by rw [Rep.add_hom, map_add]
  map_smul' a f := by rw [Rep.smul_hom, map_smul, RingHom.id_apply]
  left_inv f := by simp
  right_inv φ := by simp

variable {R : Type} [Ring R] [Algebra k R]

noncomputable def congrRight' (T : Type) [AddCommGroup T] [Module R T]
    {M₁ M₂ : Type} [AddCommGroup M₁] [Module R M₁] [Module k M₁] [IsScalarTower k R M₁]
    [AddCommGroup M₂] [Module R M₂] [Module k M₂] [IsScalarTower k R M₂]
    (e : M₁ ≃ₗ[R] M₂) : (T →ₗ[R] M₁) ≃ₗ[k] (T →ₗ[R] M₂) where
  toFun f := e.toLinearMap ∘ₗ f
  invFun f := e.symm.toLinearMap ∘ₗ f
  map_add' f g := LinearMap.comp_add _ _ _
  map_smul' a f := by
    apply LinearMap.ext; intro t
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.smul_apply, RingHom.id_apply]
    exact LinearMap.map_smul_of_tower e.toLinearMap a (f t)
  left_inv f := by apply LinearMap.ext; intro t; simp
  right_inv f := by apply LinearMap.ext; intro t; simp

noncomputable def congrLeft' {T₁ T₂ : Type} [AddCommGroup T₁] [Module R T₁] [AddCommGroup T₂] [Module R T₂]
    (M : Type) [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
    (e : T₁ ≃ₗ[R] T₂) : (T₁ →ₗ[R] M) ≃ₗ[k] (T₂ →ₗ[R] M) where
  toFun f := f ∘ₗ e.symm.toLinearMap
  invFun f := f ∘ₗ e.toLinearMap
  map_add' f g := LinearMap.add_comp _ _ _
  map_smul' a f := rfl
  left_inv f := by apply LinearMap.ext; intro t; simp
  right_inv f := by apply LinearMap.ext; intro t; simp

noncomputable def homProdEquiv (T : Type) [AddCommGroup T] [Module R T]
    (M₁ M₂ : Type) [AddCommGroup M₁] [Module R M₁] [Module k M₁] [IsScalarTower k R M₁]
    [AddCommGroup M₂] [Module R M₂] [Module k M₂] [IsScalarTower k R M₂] :
    (T →ₗ[R] M₁ × M₂) ≃ₗ[k] (T →ₗ[R] M₁) × (T →ₗ[R] M₂) where
  toFun f := ((LinearMap.fst R M₁ M₂) ∘ₗ f, (LinearMap.snd R M₁ M₂) ∘ₗ f)
  invFun fg := LinearMap.prod fg.1 fg.2
  map_add' f g := rfl
  map_smul' a f := rfl
  left_inv f := by apply LinearMap.ext; intro t; rfl
  right_inv fg := by rfl

lemma moduleFinite_hom (T : Type) [AddCommGroup T] [Module R T] [Module k T] [IsScalarTower k R T]
    (M : Type) [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [Module.Finite k M]
    [Module.Finite k T] : Module.Finite k (T →ₗ[R] M) :=
  Module.Finite.of_injective (LinearMap.restrictScalarsₗ k R T M k) (LinearMap.restrictScalars_injective k)

end homs
p2m_reactivate "P2MW.S_Rep_nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq.P2mS25DecompWD"

section core

variable (k : Type) [Field k] {R : Type} [Ring R] [Algebra k R]

noncomputable def act (M : Type) [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] (x : R) :
    M →ₗ[k] M :=
  Module.toModuleEnd k (S := R) M x

@[scoped simp] lemma act_apply (M : Type) [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
    (x : R) (m : M) : act k M x m = x • m := rfl

lemma trace_act_eq_of_linearEquiv {M₁ M₂ : Type}
    [AddCommGroup M₁] [Module R M₁] [Module k M₁] [IsScalarTower k R M₁]
    [AddCommGroup M₂] [Module R M₂] [Module k M₂] [IsScalarTower k R M₂]
    (e : M₁ ≃ₗ[R] M₂) (x : R) :
    LinearMap.trace k M₁ (act k M₁ x) = LinearMap.trace k M₂ (act k M₂ x) := by
  have : act k M₂ x = (e.restrictScalars k).conj (act k M₁ x) := by
    rw [LinearEquiv.conj_apply, LinearEquiv.eq_comp_toLinearMap_symm]
    apply LinearMap.ext
    intro m
    simp only [LinearMap.coe_comp, Function.comp_apply, act_apply, LinearEquiv.coe_coe,
      LinearEquiv.restrictScalars_apply, LinearEquiv.map_smul]
  rw [this, LinearMap.trace_conj']

lemma act_prod (M₁ M₂ : Type)
    [AddCommGroup M₁] [Module R M₁] [Module k M₁] [IsScalarTower k R M₁]
    [AddCommGroup M₂] [Module R M₂] [Module k M₂] [IsScalarTower k R M₂] (x : R) :
    act k (M₁ × M₂) x = LinearMap.prodMap (act k M₁ x) (act k M₂ x) := by
  apply LinearMap.ext; intro m; rfl

variable {ι : Type} [Fintype ι] (Tm : ι → Type) [∀ j, AddCommGroup (Tm j)] [∀ j, Module R (Tm j)]
  [∀ j, Module k (Tm j)] [∀ j, IsScalarTower k R (Tm j)] [∀ j, Module.Finite k (Tm j)]

omit [Fintype ι] [∀ j, Module.Finite k (Tm j)] in

lemma finrank_hom_simple (hsimple : ∀ j, IsSimpleModule R (Tm j))
    (hne : ∀ i j, Nonempty (Tm i ≃ₗ[R] Tm j) → i = j)
    {U : Type} [AddCommGroup U] [Module R U] [Module k U] [IsScalarTower k R U]
    {c : ι} (eU : U ≃ₗ[R] Tm c) (j : ι) :
    Module.finrank k (Tm j →ₗ[R] U) = if j = c then Module.finrank k (Tm c →ₗ[R] Tm c) else 0 := by
  rw [LinearEquiv.finrank_eq (congrRight' (Tm j) eU)]
  split_ifs with hjc
  · subst hjc; rfl
  · haveI := hsimple j
    haveI := hsimple c
    haveI : Subsingleton (Tm j →ₗ[R] Tm c) := ⟨fun f g => by
      have hf : ∀ φ : Tm j →ₗ[R] Tm c, φ = 0 := fun φ => by
        rcases LinearMap.bijective_or_eq_zero φ with h | h
        · exact absurd (hne j c ⟨LinearEquiv.ofBijective φ h⟩) hjc
        · exact h
      rw [hf f, hf g]⟩
    exact Module.finrank_zero_of_subsingleton

theorem exists_mult (hsimple : ∀ j, IsSimpleModule R (Tm j))
    (hne : ∀ i j, Nonempty (Tm i ≃ₗ[R] Tm j) → i = j)
    (hcomplete : ∀ (U : Type) [AddCommGroup U] [Module R U], IsSimpleModule R U → ∃ j, Nonempty (U ≃ₗ[R] Tm j)) :
    ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
      [Module.Finite k M] [IsSemisimpleModule R M], Module.finrank k M = n →
      ∃ m : ι → ℕ, (∀ j, Module.finrank k (Tm j →ₗ[R] M) = m j * Module.finrank k (Tm j →ₗ[R] Tm j)) ∧
        ∀ x : R, LinearMap.trace k M (act k M x) = ∑ j, (m j : k) * LinearMap.trace k (Tm j) (act k (Tm j) x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ _ _ _ _ hn
  by_cases htriv : Subsingleton M
  · refine ⟨0, fun j => ?_, fun x => ?_⟩
    · rw [Pi.zero_apply, zero_mul]
      exact Module.finrank_zero_of_subsingleton
    · have : act k M x = 0 := LinearMap.ext fun m => Subsingleton.elim _ _
      simp [this]
  · haveI : Nontrivial M := not_subsingleton_iff_nontrivial.mp htriv

    obtain ⟨U, hU⟩ := IsSemisimpleModule.exists_simple_submodule (R := R) (M := M)
    haveI := hU
    obtain ⟨W, hUW⟩ := exists_isCompl U
    let e : (U × W) ≃ₗ[R] M := Submodule.prodEquivOfIsCompl U W hUW
    haveI : Module.Finite k U := Module.Finite.of_injective (U.subtype.restrictScalars k) U.injective_subtype
    haveI : Module.Finite k W := Module.Finite.of_injective (W.subtype.restrictScalars k) W.injective_subtype
    haveI : Nontrivial U := IsSimpleModule.nontrivial R U

    have hdim : Module.finrank k M = Module.finrank k U + Module.finrank k W := by
      rw [← LinearEquiv.finrank_eq (e.restrictScalars k), Module.finrank_prod]
    have hUpos : 0 < Module.finrank k U := Module.finrank_pos
    have hW : Module.finrank k W < n := by omega
    obtain ⟨mW, hmW, htW⟩ := ih _ hW W rfl

    obtain ⟨c, ⟨eU⟩⟩ := hcomplete U hU
    refine ⟨fun j => mW j + if j = c then 1 else 0, fun j => ?_, fun x => ?_⟩
    ·
      haveI : Module.Finite k (Tm j →ₗ[R] U) := moduleFinite_hom (k := k) (R := R) (Tm j) U
      haveI : Module.Finite k (Tm j →ₗ[R] W) := moduleFinite_hom (k := k) (R := R) (Tm j) W
      rw [LinearEquiv.finrank_eq ((congrRight' (Tm j) e.symm).trans (homProdEquiv (Tm j) U W)),
        Module.finrank_prod, finrank_hom_simple k Tm hsimple hne eU j, hmW j]
      beta_reduce
      split_ifs with hjc
      · subst hjc
        ring
      · ring
    ·
      rw [← trace_act_eq_of_linearEquiv k e, act_prod, LinearMap.trace_prodMap', htW x,
        trace_act_eq_of_linearEquiv k eU x]
      simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, add_mul, Finset.sum_add_distrib,
        ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring

end core
p2m_reactivate "P2MW.S_Rep_nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq.P2mS25DecompWD"

section family

variable (R : Type) [Ring R] [IsSemisimpleRing R]

theorem exists_family : ∃ (s : ℕ) (Tm : Fin s → Submodule R R),
    (∀ j, IsSimpleModule R (Tm j)) ∧ (∀ i j, Nonempty (Tm i ≃ₗ[R] Tm j) → i = j) ∧
    ∀ (U : Type) [AddCommGroup U] [Module R U], IsSimpleModule R U → ∃ j, Nonempty (U ≃ₗ[R] Tm j) := by
  obtain ⟨n, Sf, e, hS⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp R R

  let r : Setoid (Fin n) :=
    { r := fun i j => Nonempty (Sf i ≃ₗ[R] Sf j)
      iseqv := ⟨fun i => ⟨LinearEquiv.refl R _⟩, fun ⟨f⟩ => ⟨f.symm⟩, fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩⟩ }
  let Q := Quotient r
  haveI : Fintype Q := Quotient.fintype r
  let φ : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  let rep : Fin (Fintype.card Q) → Fin n := fun a => (φ.symm a).out
  refine ⟨Fintype.card Q, fun a => Sf (rep a), fun a => hS (rep a), fun a b ⟨f⟩ => ?_, fun U _ _ hU => ?_⟩
  ·
    have hab : (Quotient.mk r (rep a) : Q) = Quotient.mk r (rep b) := Quotient.sound ⟨f⟩
    rw [Quotient.out_eq, Quotient.out_eq] at hab
    exact φ.symm.injective hab
  ·
    haveI := hU
    haveI : Nontrivial U := IsSimpleModule.nontrivial R U
    obtain ⟨u, hu⟩ := exists_ne (0 : U)
    let g : (Π₀ i, Sf i) →ₗ[R] U := (LinearMap.toSpanSingleton R U u) ∘ₗ e.symm.toLinearMap
    have hg : Function.Surjective g :=
      (IsSimpleModule.toSpanSingleton_surjective R hu).comp e.symm.surjective
    have hex : ∃ i, g ∘ₗ DFinsupp.lsingle i ≠ 0 := by
      by_contra h
      push Not at h
      have : g = 0 := DFinsupp.lhom_ext' h
      obtain ⟨y, hy⟩ := hg u
      rw [this, LinearMap.zero_apply] at hy
      exact hu hy.symm
    obtain ⟨i, hi⟩ := hex
    haveI := hS i
    have hbij := LinearMap.bijective_of_ne_zero hi

    have hrep : Nonempty (Sf (rep (φ (Quotient.mk r i))) ≃ₗ[R] Sf i) := by
      show r.r (rep (φ (Quotient.mk r i))) i
      have : rep (φ (Quotient.mk r i)) = (Quotient.mk r i).out := by
        simp only [rep, Equiv.symm_apply_apply]
      rw [this]
      exact Quotient.mk_out i
    obtain ⟨f⟩ := hrep
    exact ⟨φ (Quotient.mk r i), ⟨(LinearEquiv.ofBijective _ hbij).symm.trans f.symm⟩⟩

end family
p2m_reactivate "P2MW.S_Rep_nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq.P2mS25DecompWD"

section rep
variable (k : Type) [Field k] (G : Type) [Group G]

lemma trace_rho_eq (V : Rep.{0} k G) (g : G) :
    LinearMap.trace k V (V.ρ g) = LinearMap.trace k V.ρ.asModule (act k V.ρ.asModule (MonoidAlgebra.of k G g)) := by
  have : V.ρ g = V.ρ.asModuleEquiv.conj (act k V.ρ.asModule (MonoidAlgebra.of k G g)) := by
    rw [LinearEquiv.conj_apply, LinearEquiv.eq_comp_toLinearMap_symm]
    apply LinearMap.ext
    intro m
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, act_apply,
      Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
  rw [this, LinearMap.trace_conj']

end rep
p2m_reactivate "P2MW.S_Rep_nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq.P2mS25DecompWD"

end SST
p2m_reactivate "P2MW.S_Rep_nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq.P2mS25DecompWD P2MW.S_Rep_nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq.SST"

namespace P2mS25MarksModP

open P2mS25DecompWD SST
open scoped TensorProduct Pointwise

section Detect

variable (k : Type) [Field k] {R : Type} [Ring R] [Algebra k R] [IsSemisimpleRing R]
variable {ι : Type} [Fintype ι] (Tm : ι → Type) [∀ j, AddCommGroup (Tm j)] [∀ j, Module R (Tm j)]
  [∀ j, Module k (Tm j)] [∀ j, IsScalarTower k R (Tm j)] [∀ j, Module.Finite k (Tm j)]

theorem nonempty_linearEquiv_of_finrank_hom_eq (hsimple : ∀ j, IsSimpleModule R (Tm j))
    (hne : ∀ i j, Nonempty (Tm i ≃ₗ[R] Tm j) → i = j)
    (hcomplete : ∀ (U : Type) [AddCommGroup U] [Module R U], IsSimpleModule R U → ∃ j, Nonempty (U ≃ₗ[R] Tm j)) :
    ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [Module.Finite k M]
      (M' : Type) [AddCommGroup M'] [Module R M'] [Module k M'] [IsScalarTower k R M'] [Module.Finite k M'],
      Module.finrank k M = n →
      (∀ j, Module.finrank k (Tm j →ₗ[R] M) = Module.finrank k (Tm j →ₗ[R] M')) →
      Nonempty (M ≃ₗ[R] M') := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ _ _ _ M' _ _ _ _ _ hn hhom
  haveI : IsSemisimpleModule R M := inferInstance
  haveI : IsSemisimpleModule R M' := inferInstance

  have key : ∀ (c : ι), 0 < Module.finrank k (Tm c →ₗ[R] M') →
      ∃ U' : Submodule R M', Nonempty (U' ≃ₗ[R] Tm c) := fun c hc => by
    haveI := SST.moduleFinite_hom (k := k) (R := R) (Tm c) M'
    obtain ⟨φ, hφ⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hc
    haveI := hsimple c
    have hinj : Function.Injective φ := (LinearMap.injective_or_eq_zero φ).resolve_right hφ
    exact ⟨LinearMap.range φ, ⟨(LinearEquiv.ofInjective φ hinj).symm⟩⟩
  by_cases hM : Subsingleton M
  ·
    haveI := hM
    suffices hM' : Subsingleton M' from ⟨LinearEquiv.ofSubsingleton M M'⟩
    by_contra hns
    haveI : Nontrivial M' := not_subsingleton_iff_nontrivial.1 hns
    obtain ⟨U, hU⟩ := IsSemisimpleModule.exists_simple_submodule R M'
    obtain ⟨c, ⟨eU⟩⟩ := hcomplete U hU
    haveI := SST.moduleFinite_hom (k := k) (R := R) (Tm c) M'
    have h1 : 0 < Module.finrank k (Tm c →ₗ[R] M') := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      refine ⟨U.subtype ∘ₗ eU.symm.toLinearMap, fun h0 => ?_⟩
      haveI := hU
      haveI : Nontrivial U := IsSimpleModule.nontrivial R U
      obtain ⟨u, hu⟩ := exists_ne (0 : U)
      have := LinearMap.congr_fun h0 (eU u)
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply,
        Submodule.coe_subtype, LinearMap.zero_apply, ZeroMemClass.coe_eq_zero] at this
      exact hu this
    have h2 : Module.finrank k (Tm c →ₗ[R] M) = 0 := by
      haveI : Subsingleton (Tm c →ₗ[R] M) := ⟨fun f g => LinearMap.ext fun x => Subsingleton.elim _ _⟩
      exact Module.finrank_zero_of_subsingleton
    have := hhom c
    omega
  · haveI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    obtain ⟨U, hU⟩ := IsSemisimpleModule.exists_simple_submodule R M
    haveI := hU
    obtain ⟨W, hUW⟩ := exists_isCompl U
    let e : (U × W) ≃ₗ[R] M := Submodule.prodEquivOfIsCompl U W hUW
    haveI : Module.Finite k U := Module.Finite.of_injective (U.subtype.restrictScalars k) U.injective_subtype
    haveI : Module.Finite k W := Module.Finite.of_injective (W.subtype.restrictScalars k) W.injective_subtype
    haveI : Nontrivial U := IsSimpleModule.nontrivial R U
    have hdim : Module.finrank k M = Module.finrank k U + Module.finrank k W := by
      rw [← LinearEquiv.finrank_eq (e.restrictScalars k), Module.finrank_prod]
    have hUpos : 0 < Module.finrank k U := Module.finrank_pos
    have hWlt : Module.finrank k W < n := by omega
    obtain ⟨c, ⟨eU⟩⟩ := hcomplete U hU

    have hcpos : 0 < Module.finrank k (Tm c →ₗ[R] M') := by
      rw [← hhom c]
      haveI := SST.moduleFinite_hom (k := k) (R := R) (Tm c) U
      haveI := SST.moduleFinite_hom (k := k) (R := R) (Tm c) W
      rw [LinearEquiv.finrank_eq ((congrRight' (Tm c) e.symm).trans (homProdEquiv (Tm c) U W)), Module.finrank_prod,
        finrank_hom_simple k Tm hsimple hne eU c, if_pos rfl]
      haveI := hsimple c
      haveI : Nontrivial (Tm c) := IsSimpleModule.nontrivial R (Tm c)
      haveI := SST.moduleFinite_hom (k := k) (R := R) (Tm c) (Tm c)
      have : 0 < Module.finrank k (Tm c →ₗ[R] Tm c) :=
        Module.finrank_pos_iff_exists_ne_zero.2 ⟨LinearMap.id, fun h0 => by
          obtain ⟨t, ht⟩ := exists_ne (0 : Tm c); exact ht (LinearMap.congr_fun h0 t)⟩
      omega
    obtain ⟨U', ⟨eU'⟩⟩ := key c hcpos
    haveI : IsSimpleModule R U' := IsSimpleModule.congr eU'
    obtain ⟨W', hUW'⟩ := exists_isCompl U'
    let e' : (U' × W') ≃ₗ[R] M' := Submodule.prodEquivOfIsCompl U' W' hUW'
    haveI : Module.Finite k U' := Module.Finite.of_injective (U'.subtype.restrictScalars k) U'.injective_subtype
    haveI : Module.Finite k W' := Module.Finite.of_injective (W'.subtype.restrictScalars k) W'.injective_subtype

    have hhomW : ∀ j, Module.finrank k (Tm j →ₗ[R] W) = Module.finrank k (Tm j →ₗ[R] W') := fun j => by
      have h1 := hhom j
      haveI := SST.moduleFinite_hom (k := k) (R := R) (Tm j) U
      haveI := SST.moduleFinite_hom (k := k) (R := R) (Tm j) W
      haveI := SST.moduleFinite_hom (k := k) (R := R) (Tm j) U'
      haveI := SST.moduleFinite_hom (k := k) (R := R) (Tm j) W'
      rw [LinearEquiv.finrank_eq ((congrRight' (Tm j) e.symm).trans (homProdEquiv (Tm j) U W)), Module.finrank_prod,
        finrank_hom_simple k Tm hsimple hne eU j,
        LinearEquiv.finrank_eq ((congrRight' (Tm j) e'.symm).trans (homProdEquiv (Tm j) U' W')), Module.finrank_prod,
        finrank_hom_simple k Tm hsimple hne eU' j] at h1
      omega
    obtain ⟨eW⟩ := ih _ hWlt W W' rfl hhomW
    exact ⟨e.symm ≪≫ₗ (eU ≪≫ₗ eU'.symm).prodCongr eW ≪≫ₗ e'⟩

end Detect
p2m_reactivate "P2MW.S_Rep_nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq.P2mS25DecompWD P2MW.S_Rep_nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq.SST"

end P2mS25MarksModP
p2m_reactivate "P2MW.S_Rep_nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq.P2mS25DecompWD P2MW.S_Rep_nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq.SST"

namespace P2mS25MarksModP
open P2mS25DecompWD SST
open scoped TensorProduct Pointwise

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime]

lemma finite_red (V : Type) [AddCommGroup V] [Module.Finite ℤ V] : Module.Finite (ZMod p) (Red p V) := by
  obtain ⟨s, hs⟩ := (inferInstance : Module.Finite ℤ V)
  refine ⟨⟨s.image (Submodule.Quotient.mk (p := pSub p V)), ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    have hv : v ∈ Submodule.span ℤ (s : Set V) := by rw [hs]; exact Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem w hw =>
      exact Submodule.subset_span (by rw [Finset.coe_image]; exact ⟨w, hw, rfl⟩)
    | zero => rw [Submodule.Quotient.mk_zero]; exact Submodule.zero_mem _
    | add u w _ _ hu hw => rw [Submodule.Quotient.mk_add]; exact Submodule.add_mem _ hu hw
    | smul n w _ hw =>
      rw [Submodule.Quotient.mk_smul, ← Int.cast_smul_eq_zsmul (ZMod p) n]
      exact Submodule.smul_mem _ _ hw

lemma finrank_H0_res_res {V : Type} [AddCommGroup V] (ρ : Representation ℤ G V) (H : Subgroup G) (H' : Subgroup H) :
    Module.finrank ℤ (groupCohomology (Rep.res H'.subtype (Rep.res H.subtype (Rep.of ρ))) 0) =
      Module.finrank ℤ (groupCohomology (Rep.res (H'.map H.subtype).subtype (Rep.of ρ)) 0) := by
  have hinv : (Rep.res H'.subtype (Rep.res H.subtype (Rep.of ρ))).ρ.invariants =
      (Rep.res (H'.map H.subtype).subtype (Rep.of ρ)).ρ.invariants := by
    ext v
    simp only [Representation.mem_invariants]
    constructor
    · rintro hv ⟨_, ⟨h', hh', rfl⟩⟩
      exact hv ⟨h', hh'⟩
    · intro hv h'
      exact hv ⟨H.subtype h', Subgroup.mem_map_of_mem _ h'.2⟩
  let A₁ : Rep ℤ H' := Rep.res H'.subtype (Rep.res H.subtype (Rep.of ρ))
  let A₂ : Rep ℤ (H'.map H.subtype) := Rep.res (H'.map H.subtype).subtype (Rep.of ρ)
  let e₁ : groupCohomology A₁ 0 ≃+ A₁.ρ.invariants := (groupCohomology.H0Iso A₁).toLinearEquiv.toAddEquiv
  let e₂ : groupCohomology A₂ 0 ≃+ A₂.ρ.invariants := (groupCohomology.H0Iso A₂).toLinearEquiv.toAddEquiv
  let e₁₂ : A₁.ρ.invariants ≃+ A₂.ρ.invariants := (LinearEquiv.ofEq _ _ hinv).toAddEquiv
  let E : groupCohomology A₁ 0 ≃+ groupCohomology A₂ 0 := e₁.trans (e₁₂.trans e₂.symm)
  exact LinearEquiv.finrank_eq E.toIntLinearEquiv

section ResIso

variable (p)
variable {V V' : Type} [AddCommGroup V] [AddCommGroup V'] (ρ : Representation ℤ G V) (ρ' : Representation ℤ G V')

theorem nonempty_iso_red_of_iso_tensor {H : Type} [Group H] (σ : Representation ℤ H V) (σ' : Representation ℤ H V')
    (i : Rep.of σ ⊗ Rep.trivial ℤ H (ZMod p) ≅ Rep.of σ' ⊗ Rep.trivial ℤ H (ZMod p)) :
    Nonempty (Rep.of (redRep p V σ) ≅ Rep.of (redRep p V' σ')) := by

  let EH : V ⊗[ℤ] ZMod p ≃ₗ[ℤ] V' ⊗[ℤ] ZMod p :=
    LinearEquiv.ofLinear i.hom.hom.toLinearMap i.inv.hom.toLinearMap
      (LinearMap.ext fun x => Rep.hom_inv_apply _ _ i x) (LinearMap.ext fun x => Rep.inv_hom_apply _ _ i x)
  have hEH : ∀ h x, EH (TensorProduct.map (σ h) LinearMap.id x) = TensorProduct.map (σ' h) LinearMap.id (EH x) :=
    fun h x => Rep.hom_comm_apply i.hom h x

  let E₀ : Red p V ≃ₗ[ℤ] Red p V' := (tensorRedEquiv p V).symm ≪≫ₗ EH ≪≫ₗ tensorRedEquiv p V'
  have hE₀ : ∀ h y, E₀ (redRep p V σ h y) = redRep p V' σ' h (E₀ y) := fun h y => by
    obtain ⟨x, rfl⟩ := (tensorRedEquiv p V).surjective y
    change toRed p V' (EH ((tensorRedEquiv p V).symm (redMap p (σ h) (tensorRedEquiv p V x)))) =
      redMap p (σ' h) (toRed p V' (EH ((tensorRedEquiv p V).symm (tensorRedEquiv p V x))))
    rw [tensorRedEquiv_apply, ← toRed_natural p (σ h) x, ← tensorRedEquiv_apply p V, LinearEquiv.symm_apply_apply,
      ← tensorRedEquiv_apply p V, LinearEquiv.symm_apply_apply, hEH, toRed_natural]

  let E₁ : Red p V ≃ₗ[ZMod p] Red p V' :=
    LinearEquiv.ofBijective ((E₀ : Red p V →+ Red p V').toZModLinearMap p) E₀.bijective
  refine ⟨Rep.mkIso (Representation.Equiv.mk E₁ (fun h => LinearMap.ext fun y => hE₀ h y))⟩

end ResIso
p2m_reactivate "P2MW.S_Rep_nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq.P2mS25DecompWD P2MW.S_Rep_nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq.SST"

end P2mS25MarksModP
p2m_reactivate "P2MW.S_Rep_nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq.P2mS25DecompWD P2MW.S_Rep_nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq.SST"

open scoped TensorProduct in
open P2mS25DecompWD P2mS25MarksModP SST in

theorem solution
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hG : (Nat.card G).Coprime p)
    (L L' : Rep.{0} ℤ G) [Module.Finite ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L'] [Module.Free ℤ L']
    (h : ∀ H : Subgroup G, Module.finrank ℤ (groupCohomology (Rep.res H.subtype L) 0) =
      Module.finrank ℤ (groupCohomology (Rep.res H.subtype L') 0)) :
    Nonempty (L ⊗ Rep.trivial ℤ G (ZMod p) ≅ L' ⊗ Rep.trivial ℤ G (ZMod p)) := by

  cases L; rename_i V hV1 hV2 ρ hVfin hVfree
  have h2 : hV2 = AddCommGroup.toIntModule V := Subsingleton.elim _ _
  subst h2
  cases L'; rename_i V' hV1' hV2' ρ' hVfin' hVfree'
  have h2' : hV2' = AddCommGroup.toIntModule V' := Subsingleton.elim _ _
  subst h2'
  haveI : Module.Free ℤ V := hVfree
  haveI : Module.Free ℤ V' := hVfree'
  haveI : Module.Finite ℤ V := hVfin
  haveI : Module.Finite ℤ V' := hVfin'
  haveI : NeZero ((Nat.card G : ℕ) : ZMod p) := ⟨by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hG.symm⟩
  haveI : Module.Finite (ZMod p) (Red p V) := finite_red V
  haveI : Module.Finite (ZMod p) (Red p V') := finite_red V'

  let A : Rep.{0} (ZMod p) G := Rep.of (redRep p V ρ)
  let B : Rep.{0} (ZMod p) G := Rep.of (redRep p V' ρ')
  haveI : FiniteDimensional (ZMod p) A := (inferInstance : Module.Finite (ZMod p) (Red p V))
  haveI : FiniteDimensional (ZMod p) B := (inferInstance : Module.Finite (ZMod p) (Red p V'))

  have hres : ∀ H : Subgroup G, IsCyclic H → (Nat.card H).Coprime p →
      Nonempty (Rep.res H.subtype A ≅ Rep.res H.subtype B) := by
    intro H hH hHp
    haveI := hH
    haveI : Module.Finite ℤ (Rep.res H.subtype (Rep.of ρ) : Rep ℤ H) := hVfin
    haveI : Module.Free ℤ (Rep.res H.subtype (Rep.of ρ) : Rep ℤ H) := hVfree
    haveI : Module.Finite ℤ (Rep.res H.subtype (Rep.of ρ') : Rep ℤ H) := hVfin'
    haveI : Module.Free ℤ (Rep.res H.subtype (Rep.of ρ') : Rep ℤ H) := hVfree'
    have hmarks : ∀ H' : Subgroup H,
        Module.finrank ℤ (groupCohomology (Rep.res H'.subtype (Rep.res H.subtype (Rep.of ρ))) 0) =
          Module.finrank ℤ (groupCohomology (Rep.res H'.subtype (Rep.res H.subtype (Rep.of ρ'))) 0) := fun H' => by
      rw [finrank_H0_res_res, finrank_H0_res_res, h]
    obtain ⟨f, hf, hfi⟩ := Rep.exists_hom_injective_finiteIndex_of_finrank_invariants_eq
      (Rep.res H.subtype (Rep.of ρ)) (Rep.res H.subtype (Rep.of ρ')) hmarks
    obtain ⟨i⟩ := Rep.nonempty_tensor_trivial_zmod_iso_of_injective_of_finiteIndex hHp
      (Rep.res H.subtype (Rep.of ρ)) (Rep.res H.subtype (Rep.of ρ')) f hf hfi
    exact nonempty_iso_red_of_iso_tensor p (ρ.comp H.subtype) (ρ'.comp H.subtype) i

  have hhomT : ∀ (T : Rep.{0} (ZMod p) G) [FiniteDimensional (ZMod p) T],
      Module.finrank (ZMod p) (T ⟶ A) = Module.finrank (ZMod p) (T ⟶ B) := by
    intro T _
    have := Rep.eq_of_additive_of_forall_nonempty_res_iso (fun X => (Module.finrank (ZMod p) (T ⟶ X) : ℤ))
      (fun X hX hfin => by
        haveI := hfin
        show ((Module.finrank (ZMod p) (T ⟶ X.X₂) : ℤ)) =
          (Module.finrank (ZMod p) (T ⟶ X.X₁) : ℤ) + (Module.finrank (ZMod p) (T ⟶ X.X₃) : ℤ)
        exact_mod_cast Rep.finrank_hom_eq_add_of_shortExact_of_card_coprime hG T X hX) A B hres
    exact_mod_cast (show ((Module.finrank (ZMod p) (T ⟶ A) : ℤ)) = (Module.finrank (ZMod p) (T ⟶ B) : ℤ) from this)

  haveI : IsSemisimpleRing (MonoidAlgebra (ZMod p) G) := inferInstance
  obtain ⟨s, Tm, hsimple, hne, hcomplete⟩ := SST.exists_family (MonoidAlgebra (ZMod p) G)
  haveI hfin : ∀ j, Module.Finite (ZMod p) (Tm j) := fun j =>
    Module.Finite.of_injective ((Tm j).subtype.restrictScalars (ZMod p)) (Tm j).injective_subtype
  have hhom : ∀ j, Module.finrank (ZMod p) (Tm j →ₗ[MonoidAlgebra (ZMod p) G] X p ρ) =
      Module.finrank (ZMod p) (Tm j →ₗ[MonoidAlgebra (ZMod p) G] X p ρ') := fun j => by
    haveI := hsimple j
    let T : Rep.{0} (ZMod p) G := Rep.of (SST.repOfModule (ZMod p) G (Tm j))
    haveI : FiniteDimensional (ZMod p) T := hfin j
    have hT := hhomT T
    rw [LinearEquiv.finrank_eq ((SST.homEquivLinearMap T A).trans
          (SST.congrLeft' (X p ρ) (SST.asModuleEquiv' (ZMod p) G (Tm j)))),
        LinearEquiv.finrank_eq ((SST.homEquivLinearMap T B).trans
          (SST.congrLeft' (X p ρ') (SST.asModuleEquiv' (ZMod p) G (Tm j))))] at hT
    exact hT
  obtain ⟨e⟩ := nonempty_linearEquiv_of_finrank_hom_eq (ZMod p) (fun j => (Tm j : Type)) hsimple hne hcomplete _
    (X p ρ) (X p ρ') rfl hhom

  let E₀ : Red p V ≃ₗ[ℤ] Red p V' := e.toAddEquiv.toIntLinearEquiv
  have hE₀ : ∀ g (x : Red p V), E₀ (redRep p V ρ g x) = redRep p V' ρ' g (E₀ x) := fun g x => by
    show e (redRep p V ρ g x) = redRep p V' ρ' g (e x)
    have h1 : ∀ (W : Type _) [AddCommGroup W] (σ : Representation ℤ G W) (y : X p σ),
        (MonoidAlgebra.single g (1 : ZMod p)) • y = redRep p W σ g y := fun W _ σ y => by
      rw [Representation.single_smul, one_smul]; rfl
    rw [← h1 V ρ x, map_smul, h1 V' ρ']
  let E : V ⊗[ℤ] ZMod p ≃ₗ[ℤ] V' ⊗[ℤ] ZMod p :=
    tensorRedEquiv p V ≪≫ₗ E₀ ≪≫ₗ (tensorRedEquiv p V').symm
  have hnat' : ∀ g (y : Red p V'), (tensorRedEquiv p V').symm (redRep p V' ρ' g y) =
      TensorProduct.map (ρ' g) LinearMap.id ((tensorRedEquiv p V').symm y) := fun g y => by
    apply (tensorRedEquiv p V').injective
    rw [LinearEquiv.apply_symm_apply, tensorRedEquiv_apply, toRed_natural, ← tensorRedEquiv_apply,
      LinearEquiv.apply_symm_apply]
    rfl
  refine ⟨Rep.mkIso (Representation.Equiv.mk E (fun g => ?_))⟩
  apply LinearMap.ext
  intro x
  show E (TensorProduct.map (ρ g) LinearMap.id x) = TensorProduct.map (ρ' g) LinearMap.id (E x)
  simp only [E, LinearEquiv.trans_apply, tensorRedEquiv_apply]
  rw [toRed_natural, ← hnat', ← hE₀]
  rfl

end S_Rep_nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq
end P2MW
export P2MW.S_Rep_nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq (solution)
