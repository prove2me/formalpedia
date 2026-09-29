-- Prove2me | solution 1 for Rep.nonempty_tensor_trivial_zmod_iso_of_injective_of_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/cd474e9d-b7f5-5221-ac64-4b3c67adf123

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_nonempty_tensor_trivial_zmod_iso_of_injective_of_finiteIndex

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

section Steps

variable (p)
variable {V : Type*} [AddCommGroup V] (ρ : Representation ℤ G V)

local notation "R" => MonoidAlgebra (ZMod p) G

theorem nonempty_linearEquiv_of_circular {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [IsSemisimpleModule R M] [IsSemisimpleModule R N]
    (i : M →ₗ[R] N) (π : N →ₗ[R] M) (h1 : LinearMap.ker i = LinearMap.range π)
    (h2 : LinearMap.ker π = LinearMap.range i) : Nonempty (M ≃ₗ[R] N) := by
  obtain ⟨C, hC⟩ := exists_isCompl (LinearMap.ker i)
  obtain ⟨D, hD⟩ := exists_isCompl (LinearMap.ker π)

  let eM : M ≃ₗ[R] (LinearMap.range π) × (LinearMap.range i) :=
    (Submodule.prodEquivOfIsCompl _ _ hC).symm ≪≫ₗ
      ((LinearEquiv.ofEq _ _ h1).prodCongr
        ((Submodule.quotientEquivOfIsCompl _ C hC).symm ≪≫ₗ i.quotKerEquivRange))

  let eN : N ≃ₗ[R] (LinearMap.range i) × (LinearMap.range π) :=
    (Submodule.prodEquivOfIsCompl _ _ hD).symm ≪≫ₗ
      ((LinearEquiv.ofEq _ _ h2).prodCongr
        ((Submodule.quotientEquivOfIsCompl _ D hD).symm ≪≫ₗ π.quotKerEquivRange))
  exact ⟨eM ≪≫ₗ LinearEquiv.prodComm R _ _ ≪≫ₗ eN.symm⟩

variable [Module.IsTorsionFree ℤ V]

theorem nonempty_equiv_divP [Finite G] [NeZero ((Nat.card G : ℕ) : ZMod p)]
    (S : Submodule ℤ V) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) :
    Nonempty (X p (subRep ρ S hS) ≃ₗ[R] X p (subRep ρ (divP p S) (divP_stable p ρ S hS))) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  let i := incl p ρ S (divP p S) hS (divP_stable p ρ S hS) (le_divP p S)
  let π := mulP p ρ S hS
  refine nonempty_linearEquiv_of_circular p i π ?_ ?_
  ·
    apply le_antisymm
    · intro x hx
      induction x using Submodule.Quotient.induction_on with
      | H v =>
        rw [LinearMap.mem_ker] at hx
        change (Submodule.Quotient.mk (Submodule.inclusion (le_divP p S) v) : Red p (divP p S)) = 0 at hx
        rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at hx
        obtain ⟨w, -, hw⟩ := hx
        refine ⟨Submodule.Quotient.mk w, ?_⟩
        change (Submodule.Quotient.mk _ : Red p S) = Submodule.Quotient.mk v
        congr 1
        apply Subtype.ext
        have := congrArg Subtype.val hw
        simpa [LinearMap.restrict_apply] using this
    · rintro x ⟨y, rfl⟩
      induction y using Submodule.Quotient.induction_on with
      | H w =>
        rw [LinearMap.mem_ker]
        change (Submodule.Quotient.mk (Submodule.inclusion (le_divP p S) _) : Red p (divP p S)) = 0
        have : Submodule.inclusion (le_divP p S)
            ((((p : ℤ) • LinearMap.id : V →ₗ[ℤ] V).restrict (fun v hv => (mem_divP p).1 hv)) w) = (p : ℤ) • w := by
          apply Subtype.ext; simp [LinearMap.restrict_apply]
        rw [this]
        exact p_smul_mk p _ w
  ·
    apply le_antisymm
    · intro x hx
      induction x using Submodule.Quotient.induction_on with
      | H w =>
        rw [LinearMap.mem_ker] at hx
        change (Submodule.Quotient.mk _ : Red p S) = 0 at hx
        rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at hx
        obtain ⟨v, -, hv⟩ := hx
        have hv' : (v : V) = (w : V) := by
          have := congrArg Subtype.val hv
          simp only [SetLike.val_smul, LinearMap.restrict_apply, LinearMap.smul_apply, LinearMap.id_apply] at this
          exact smul_right_injective V hp0 this
        have hwS : (w : V) ∈ S := hv' ▸ v.2
        refine ⟨Submodule.Quotient.mk ⟨w, hwS⟩, ?_⟩
        change (Submodule.Quotient.mk (Submodule.inclusion (le_divP p S) ⟨w, hwS⟩) : Red p (divP p S)) = Submodule.Quotient.mk w
        rfl
    · rintro x ⟨y, rfl⟩
      induction y using Submodule.Quotient.induction_on with
      | H v =>
        rw [LinearMap.mem_ker]
        change (Submodule.Quotient.mk _ : Red p S) = 0
        have : (((p : ℤ) • LinearMap.id : V →ₗ[ℤ] V).restrict (fun v hv => (mem_divP p).1 hv))
            (Submodule.inclusion (le_divP p S) v) = (p : ℤ) • v := by
          apply Subtype.ext; simp [LinearMap.restrict_apply]
        rw [this]
        exact p_smul_mk p _ v

theorem bijective_inclTop (S : Submodule ℤ V) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) [S.toAddSubgroup.FiniteIndex]
    (hcop : (S.toAddSubgroup.index).Coprime p) : Function.Bijective (inclTop p ρ S hS) := by
  set n := S.toAddSubgroup.index with hn

  have hb : IsCoprime (n : ℤ) (p : ℤ) := Int.isCoprime_iff_gcd_eq_one.2 (by rw [Int.gcd_natCast_natCast]; exact hcop)
  obtain ⟨a, b, hab⟩ := hb

  have hnS : ∀ v : V, (n : ℤ) • v ∈ S := fun v => by
    have : (n • (v : V ⧸ S.toAddSubgroup) : V ⧸ S.toAddSubgroup) = 0 := by
      rw [hn, AddSubgroup.index_eq_card]; exact card_nsmul_eq_zero'
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at this
    rwa [natCast_zsmul]
  have hdec : ∀ v : V, v = a • ((n : ℤ) • v) + (p : ℤ) • (b • v) := fun v => by
    rw [smul_smul, smul_smul, ← add_smul, mul_comm (p : ℤ) b, hab, one_smul]
  constructor
  ·
    rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H v =>
      change (Submodule.Quotient.mk (v : V) : Red p V) = 0 at hx
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at hx
      obtain ⟨w, -, hw⟩ := hx
      have hwS : w ∈ S := by
        rw [hdec w]
        refine S.add_mem (S.smul_mem _ (hnS w)) ?_
        rw [smul_comm, hw]
        exact S.smul_mem _ v.2
      show (Submodule.Quotient.mk v : Red p S) = 0
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨⟨w, hwS⟩, Submodule.mem_top, Subtype.ext hw⟩
  ·
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H v =>
      refine ⟨Submodule.Quotient.mk ⟨a • ((n : ℤ) • v), S.smul_mem _ (hnS v)⟩, ?_⟩
      change (Submodule.Quotient.mk (a • ((n : ℤ) • v)) : Red p V) = Submodule.Quotient.mk v
      rw [eq_comm, Submodule.Quotient.eq, Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨b • v, Submodule.mem_top, by rw [eq_sub_iff_add_eq, add_comm]; exact (hdec v).symm⟩

end Steps

section Induction

variable (p)
variable {V : Type*} [AddCommGroup V] (ρ : Representation ℤ G V) [Module.IsTorsionFree ℤ V]
variable [Finite G] [NeZero ((Nat.card G : ℕ) : ZMod p)]

local notation "R" => MonoidAlgebra (ZMod p) G

theorem nonempty_equiv_of_index :
    ∀ (n : ℕ) (S : Submodule ℤ V) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S),
      S.toAddSubgroup.index = n → S.toAddSubgroup.FiniteIndex →
      Nonempty (X p (subRep ρ S hS) ≃ₗ[R] X p ρ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hS hn hfi
  haveI := hfi
  by_cases hcop : (S.toAddSubgroup.index).Coprime p
  · exact ⟨LinearEquiv.ofBijective (inclTop p ρ S hS) (bijective_inclTop p ρ S hS hcop)⟩
  · have hdvd : p ∣ S.toAddSubgroup.index := by
      by_contra h
      exact hcop ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 h).symm

    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := V ⧸ S.toAddSubgroup) p
      (by rwa [← AddSubgroup.index_eq_card])
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective x
    have hv1 : v ∈ divP p S := by
      rw [mem_divP, natCast_zsmul]
      have h0 : ((p • v : V) : V ⧸ S.toAddSubgroup) = 0 := by
        rw [QuotientAddGroup.mk_nsmul, ← hx]; exact addOrderOf_nsmul_eq_zero _
      exact (QuotientAddGroup.eq_zero_iff _).1 h0
    have hv0 : v ∉ S := fun h => by
      have : ((v : V ⧸ S.toAddSubgroup)) = 0 := (QuotientAddGroup.eq_zero_iff v).2 h
      rw [this, addOrderOf_zero] at hx
      exact (Fact.out : p.Prime).one_lt.ne hx
    have hlt : S.toAddSubgroup < (divP p S).toAddSubgroup :=
      lt_of_le_of_ne (fun w hw => le_divP p S hw) (fun h => hv0 (by
        have : v ∈ (divP p S).toAddSubgroup := hv1
        rwa [← h] at this))
    have hidx : (divP p S).toAddSubgroup.index < n := hn ▸ AddSubgroup.index_strictAnti hlt
    have hfi' : (divP p S).toAddSubgroup.FiniteIndex := AddSubgroup.finiteIndex_of_le hlt.le
    obtain ⟨e₁⟩ := ih _ hidx (divP p S) (divP_stable p ρ S hS) rfl hfi'
    obtain ⟨e₀⟩ := nonempty_equiv_divP p ρ S hS
    exact ⟨e₀ ≪≫ₗ e₁⟩

end Induction

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
p2m_reactivate "P2MW.S_Rep_nonempty_tensor_trivial_zmod_iso_of_injective_of_finiteIndex.P2mS25DecompWD"

open scoped TensorProduct in
open P2mS25DecompWD in

theorem solution
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hG : (Nat.card G).Coprime p)
    (L L' : Rep ℤ G) [Module.Finite ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L'] [Module.Free ℤ L']
    (f : L ⟶ L') (hf : Function.Injective f.hom) (hfi : (f.hom : L →+ L').range.FiniteIndex) :
    Nonempty (L ⊗ Rep.trivial ℤ G (ZMod p) ≅ L' ⊗ Rep.trivial ℤ G (ZMod p)) := by

  cases L; rename_i V hV1 hV2 ρ hVfin hVfree
  have h2 : hV2 = AddCommGroup.toIntModule V := Subsingleton.elim _ _
  subst h2
  cases L'; rename_i V' hV1' hV2' ρ' hVfin' hVfree'
  have h2' : hV2' = AddCommGroup.toIntModule V' := Subsingleton.elim _ _
  subst h2'
  haveI : Module.Free ℤ V := hVfree
  haveI : Module.Free ℤ V' := hVfree'
  haveI : Module.IsTorsionFree ℤ V' := inferInstance
  haveI : NeZero ((Nat.card G : ℕ) : ZMod p) := ⟨by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hG.symm⟩

  let φ : V →ₗ[ℤ] V' := f.hom.toLinearMap
  have hφ : ∀ g v, φ (ρ g v) = ρ' g (φ v) := fun g v => Rep.hom_comm_apply f g v
  let S₀ : Submodule ℤ V' := LinearMap.range φ
  have hS₀ : ∀ g, ∀ w ∈ S₀, ρ' g w ∈ S₀ := by
    rintro g _ ⟨v, rfl⟩
    exact ⟨ρ g v, hφ g v⟩
  haveI hfi₀ : S₀.toAddSubgroup.FiniteIndex := by
    have : S₀.toAddSubgroup = (f.hom : V →+ V').range := by
      ext w; simp only [Submodule.mem_toAddSubgroup, LinearMap.mem_range, AddMonoidHom.mem_range]; rfl
    rw [this]; exact hfi

  have hinjφ : Function.Injective φ := hf
  let eL : X p ρ ≃ₗ[MonoidAlgebra (ZMod p) G] X p (subRep ρ' S₀ hS₀) :=
    redEquiv p ρ (subRep ρ' S₀ hS₀) (LinearEquiv.ofInjective φ hinjφ) (fun g v => by
      apply Subtype.ext
      exact hφ g v)
  obtain ⟨eI⟩ := nonempty_equiv_of_index p ρ' (S₀.toAddSubgroup.index) S₀ hS₀ rfl hfi₀
  let e := eL ≪≫ₗ eI

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

end S_Rep_nonempty_tensor_trivial_zmod_iso_of_injective_of_finiteIndex
end P2MW
export P2MW.S_Rep_nonempty_tensor_trivial_zmod_iso_of_injective_of_finiteIndex (solution)
