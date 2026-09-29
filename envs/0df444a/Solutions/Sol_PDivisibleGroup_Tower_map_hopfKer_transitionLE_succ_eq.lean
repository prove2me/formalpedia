-- Prove2me | solution 1 for PDivisibleGroup.Tower.map_hopfKer_transitionLE_succ_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/1cfe0513-df87-5ac3-9ce4-7359a9512d40

import Mathlib
import Definitions.Def_PDivisibleGroup_Tower
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
import Theorems.Thm_HopfAlgebra_map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_Tower_map_hopfKer_transitionLE_succ_eq
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false

noncomputable section

open scoped TensorProduct
open HopfAlgebra PDivisibleGroup

namespace GAMMA2

section Formal

variable {R : Type} [CommRing R]
  {A₂ A₁ C : Type} [CommRing A₂] [CommRing A₁] [CommRing C]
  [HopfAlgebra R A₂] [HopfAlgebra R A₁] [HopfAlgebra R C]
  (t : A₂ →ₐc[R] A₁) (π₁ : A₁ →ₐc[R] C)

theorem map_hopfKer_comp_le :
    (hopfKer (π₁.comp t)).map (t : A₂ →ₐ[R] A₁) ≤ hopfKer π₁ := by
  rintro _ ⟨x, hx, rfl⟩
  change x ∈ hopfKer (π₁.comp t) at hx
  rw [HopfAlgebra.mem_hopfKer_iff] at hx
  change coaction π₁ (t x) = t x ⊗ₜ[R] 1

  have hΔ : Coalgebra.comul (R := R) (t x) =
      Algebra.TensorProduct.map (t : A₂ →ₐ[R] A₁) (t : A₂ →ₐ[R] A₁) (Coalgebra.comul (R := R) x) := by
    have := congrArg (fun φ : A₂ →ₐ[R] A₁ ⊗[R] A₁ => φ x) (BialgHom.map_comp_comulAlgHom t)
    simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply] at this
    exact this.symm
  have hx' : Algebra.TensorProduct.map (AlgHom.id R A₂) ((π₁.comp t : A₂ →ₐc[R] C) : A₂ →ₐ[R] C)
      (Coalgebra.comul (R := R) x) = x ⊗ₜ[R] 1 := hx
  rw [HopfAlgebra.coaction_apply, hΔ, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
  have hcomp : ((π₁ : A₁ →ₐ[R] C).comp (t : A₂ →ₐ[R] A₁)) = ((π₁.comp t : A₂ →ₐc[R] C) : A₂ →ₐ[R] C) := rfl
  rw [AlgHom.id_comp, hcomp]
  have hsplit : Algebra.TensorProduct.map (t : A₂ →ₐ[R] A₁) ((π₁.comp t : A₂ →ₐc[R] C) : A₂ →ₐ[R] C) =
      (Algebra.TensorProduct.map (t : A₂ →ₐ[R] A₁) (AlgHom.id R C)).comp
        (Algebra.TensorProduct.map (AlgHom.id R A₂) ((π₁.comp t : A₂ →ₐc[R] C) : A₂ →ₐ[R] C)) := by
    rw [← Algebra.TensorProduct.map_comp, AlgHom.comp_id, AlgHom.id_comp]
  rw [hsplit, AlgHom.comp_apply, hx', Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem ker_eq_map_ker_comp (ht : Function.Surjective t) :
    RingHom.ker (π₁ : A₁ →ₐ[R] C) = Ideal.map (t : A₂ →ₐ[R] A₁) (RingHom.ker ((π₁.comp t : A₂ →ₐc[R] C) : A₂ →ₐ[R] C)) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := ht y
    exact Ideal.mem_map_of_mem _ (by simpa [RingHom.mem_ker] using hy)
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    simpa [RingHom.mem_ker, Ideal.mem_comap] using hx

end Formal

section BaseChange

variable {R : Type} [CommRing R] [IsLocalRing R]
  {A C : Type} [CommRing A] [CommRing C]
  [HopfAlgebra R A] [HopfAlgebra R C] [Coalgebra.IsCocomm R A]
  [Module.Finite R A] [Module.Free R A] [Module.Finite R C] [Module.Free R C]
  (π : A →ₐc[R] C) (hπ : Function.Surjective π)

local notation "k" => IsLocalRing.ResidueField R

def bc : k ⊗[R] A →ₐc[k] k ⊗[R] C := Bialgebra.TensorProduct.map (BialgHom.id k k) π

omit [Coalgebra.IsCocomm R A] [Module.Finite R A] [Module.Free R A] [Module.Finite R C]
  [Module.Free R C] in
@[scoped simp] theorem bc_tmul (s : k) (a : A) : bc π (s ⊗ₜ[R] a) = s ⊗ₜ[R] π a := rfl

include hπ in
omit [Coalgebra.IsCocomm R A] [Module.Finite R A] [Module.Free R A] [Module.Finite R C] [Module.Free R C] in
theorem bc_surjective : Function.Surjective (bc π) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul s c =>
      obtain ⟨a, rfl⟩ := hπ c
      exact ⟨s ⊗ₜ[R] a, rfl⟩
  | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩

include hπ in
omit [Coalgebra.IsCocomm R A] in

theorem finrank_hopfKer_mul [Module.Free R ↥(hopfKer π)] :
    Module.finrank R ↥(hopfKer π) * Module.finrank R C = Module.finrank R A := by
  obtain ⟨-, -, -, hrank⟩ := HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective π hπ
  have h := hrank (IsLocalRing.closedPoint R)
  rwa [Module.rankAtStalk_eq_finrank_of_free] at h

include hπ in
omit [Coalgebra.IsCocomm R A] in

theorem finrank_hopfKer_bc_mul :
    Module.finrank k ↥(hopfKer (bc π)) * Module.finrank R C = Module.finrank R A := by
  obtain ⟨-, -, -, hrank⟩ :=
    HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective (bc π) (bc_surjective π hπ)
  have h := hrank ⟨⊥, Ideal.isPrime_bot⟩
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_baseChange, Module.finrank_baseChange] at h
  exact h

omit [Module.Finite R A] [Module.Free R A] [Module.Finite R C] [Module.Free R C] in

theorem one_tmul_mem_hopfKer_bc {a : A} (ha : a ∈ hopfKer π) : (1 : k) ⊗ₜ[R] a ∈ hopfKer (bc π) := by
  rw [HopfAlgebra.mem_hopfKer_iff] at ha ⊢

  let θ : A ⊗[R] C →ₗ[R] (k ⊗[R] A) ⊗[k] (k ⊗[R] C) :=
    (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R k R k k k A C).toLinearMap.restrictScalars R ∘ₗ
      (TensorProduct.mk R (k ⊗[k] k) (A ⊗[R] C) ((1 : k) ⊗ₜ[k] (1 : k)))
  have hθ : ∀ (a' : A) (c : C), θ (a' ⊗ₜ[R] c) = ((1 : k) ⊗ₜ[R] a') ⊗ₜ[k] ((1 : k) ⊗ₜ[R] c) := fun a' c => by
    simp [θ]

  have hnat : ∀ y : A ⊗[R] A,
      Algebra.TensorProduct.map (AlgHom.id k (k ⊗[R] A)) (bc π : k ⊗[R] A →ₐ[k] k ⊗[R] C)
          (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R k R k k k A A
            (((1 : k) ⊗ₜ[k] (1 : k)) ⊗ₜ[R] y)) =
        θ (Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] C) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero, map_zero, LinearMap.map_zero]
    | tmul a₁ a₂ =>
        rw [Algebra.TensorProduct.map_tmul, hθ]
        simp [bc]
    | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy, map_add, map_add]
  have hcomul : Coalgebra.comul (R := k) ((1 : k) ⊗ₜ[R] a) =
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R k R k k k A A
        (((1 : k) ⊗ₜ[k] (1 : k)) ⊗ₜ[R] Coalgebra.comul (R := R) a) := by
    rw [TensorProduct.comul_tmul, CommSemiring.comul_apply]
  rw [HopfAlgebra.coaction_apply, hcomul, hnat, ← HopfAlgebra.coaction_apply, ha, hθ]
  rfl

theorem baseChange_hopfKer_eq [Module.Free R ↥(hopfKer π)] (hπ : Function.Surjective π) :
    (Subalgebra.toSubmodule (hopfKer π)).baseChange k = Subalgebra.toSubmodule (hopfKer (bc π)) := by
  have hle : (Subalgebra.toSubmodule (hopfKer π)).baseChange k ≤ Subalgebra.toSubmodule (hopfKer (bc π)) := by
    rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    exact one_tmul_mem_hopfKer_bc π ha
  apply Submodule.eq_of_le_of_finrank_eq hle

  obtain ⟨⟨r, hr⟩, -, -, -⟩ := HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective π hπ
  have hinj : Function.Injective ((Subalgebra.toSubmodule (hopfKer π)).subtype.baseChange k) := by

    let r' : A →ₗ[R] ↥(hopfKer π) := r.restrictScalars R
    have hsplit : r' ∘ₗ (Subalgebra.toSubmodule (hopfKer π)).subtype = LinearMap.id := by
      ext c; exact congrArg Subtype.val (hr c)
    intro x y hxy
    have := congrArg (r'.baseChange k) hxy
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hsplit,
      LinearMap.baseChange_id, LinearMap.id_apply, LinearMap.id_apply] at this
  have h1 : Module.finrank k ↥((Subalgebra.toSubmodule (hopfKer π)).baseChange k) = Module.finrank R ↥(hopfKer π) := by
    rw [Submodule.baseChange, LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange]
    rfl
  have hC : 0 < Module.finrank R C := by
    haveI : Nontrivial C := (Bialgebra.counitAlgHom R C).toRingHom.domain_nontrivial
    rw [Module.finrank_eq_card_chooseBasisIndex]
    exact Fintype.card_pos
  have h2 := finrank_hopfKer_mul π hπ
  have h3 := finrank_hopfKer_bc_mul π hπ
  rw [h1]
  exact Nat.eq_of_mul_eq_mul_right hC (h2.trans h3.symm)

end BaseChange

section Nakayama

variable {R : Type} [CommRing R] [IsLocalRing R] {M : Type} [AddCommGroup M] [Module R M]

theorem mem_sup_smul_of_one_tmul_mem_baseChange (N : Submodule R M) (m : M)
    (hm : (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] m ∈ N.baseChange (IsLocalRing.ResidueField R)) :
    m ∈ N ⊔ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R M) := by
  let e : IsLocalRing.ResidueField R ⊗[R] M ≃ₗ[R] M ⧸ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R M) :=
    TensorProduct.quotTensorEquivQuotSMul M (IsLocalRing.maximalIdeal R)
  have he_tmul : ∀ (r : R) (x : M), e ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) r) ⊗ₜ[R] x) =
      r • Submodule.Quotient.mk x := fun r x => TensorProduct.quotTensorEquivQuotSMul_mk_tmul (IsLocalRing.maximalIdeal R) r x
  have himage : ∀ z ∈ N.baseChange (IsLocalRing.ResidueField R),
      e z ∈ N.map (Submodule.mkQ ((IsLocalRing.maximalIdeal R) • (⊤ : Submodule R M))) := by
    rintro _ ⟨w, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]; exact zero_mem _
    | tmul q n =>
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
        rw [LinearMap.baseChange_tmul, Submodule.subtype_apply, he_tmul]
        exact Submodule.smul_mem _ r (Submodule.mem_map_of_mem n.2)
    | add x y hx hy => simp only [map_add]; exact add_mem hx hy
  have h1 := himage _ hm
  have he : e ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] m) = Submodule.Quotient.mk m := by
    have := he_tmul 1 m
    rwa [one_smul, map_one] at this
  have h2 : Submodule.Quotient.mk m ∈ N.map (Submodule.mkQ ((IsLocalRing.maximalIdeal R) • (⊤ : Submodule R M))) :=
    he ▸ h1
  have h3 : m ∈ Submodule.comap (Submodule.mkQ ((IsLocalRing.maximalIdeal R) • (⊤ : Submodule R M)))
      (N.map (Submodule.mkQ ((IsLocalRing.maximalIdeal R) • (⊤ : Submodule R M)))) := h2
  rwa [Submodule.comap_map_mkQ, sup_comm] at h3

end Nakayama

section Main

variable {R : Type} [CommRing R] [IsLocalRing R]
  {A₂ A₁ C : Type} [CommRing A₂] [CommRing A₁] [CommRing C]
  [HopfAlgebra R A₂] [HopfAlgebra R A₁] [HopfAlgebra R C]
  [Coalgebra.IsCocomm R A₂] [Coalgebra.IsCocomm R A₁]
  [Module.Finite R A₂] [Module.Free R A₂] [Module.Finite R A₁] [Module.Free R A₁]
  [Module.Finite R C] [Module.Free R C]
  (t : A₂ →ₐc[R] A₁) (π₁ : A₁ →ₐc[R] C) (ht : Function.Surjective t) (hπ₁ : Function.Surjective π₁)

local notation "k" => IsLocalRing.ResidueField R

omit [Coalgebra.IsCocomm R A₂] [Coalgebra.IsCocomm R A₁] [Module.Finite R A₂] [Module.Free R A₂]
  [Module.Finite R A₁] [Module.Free R A₁] [Module.Finite R C] [Module.Free R C] in
theorem bc_comp : bc (π₁.comp t) = (bc π₁).comp (bc (C := A₁) t) := by
  apply DFunLike.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s a => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

include ht hπ₁ in

theorem map_hopfKer_comp_eq [Module.Free R ↥(hopfKer π₁)] [Module.Free R ↥(hopfKer (π₁.comp t))] :
    (hopfKer (π₁.comp t)).map (t : A₂ →ₐ[R] A₁) = hopfKer π₁ := by
  apply le_antisymm (map_hopfKer_comp_le t π₁)

  set S : Submodule R A₁ := Subalgebra.toSubmodule (hopfKer π₁) with hS
  set T : Submodule R A₁ := Subalgebra.toSubmodule ((hopfKer (π₁.comp t)).map (t : A₂ →ₐ[R] A₁)) with hT
  have hTS : T ≤ S := map_hopfKer_comp_le t π₁
  have hT' : T = (Subalgebra.toSubmodule (hopfKer (π₁.comp t))).map (t : A₂ →ₐ[R] A₁).toLinearMap := by
    rw [hT, Subalgebra.map_toSubmodule]

  obtain ⟨⟨r, hr⟩, hfin, -, -⟩ :=
    HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective π₁ hπ₁
  let r' : A₁ →ₗ[R] ↥(hopfKer π₁) := r.restrictScalars R
  have hr' : ∀ c : ↥(hopfKer π₁), r' c = c := hr

  have hfield : (hopfKer (bc (π₁.comp t))).map (bc (C := A₁) t : k ⊗[R] A₂ →ₐ[k] k ⊗[R] A₁) =
      hopfKer (bc π₁) := by
    apply HopfAlgebra.map_hopfKer_eq_hopfKer_of_surjective_of_ker_eq_map_ker k (bc (C := A₁) t) (bc (π₁.comp t))
      (bc π₁) (bc_surjective t ht) (bc_surjective _ (hπ₁.comp ht)) (bc_surjective π₁ hπ₁)
    rw [bc_comp]
    exact ker_eq_map_ker_comp (bc (C := A₁) t) (bc π₁) (bc_surjective t ht)

  have hNN : (⊤ : Submodule R ↥(hopfKer π₁)) ≤ T.comap S.subtype ⊔ (IsLocalRing.maximalIdeal R) • ⊤ := by
    rintro y -
    apply mem_sup_smul_of_one_tmul_mem_baseChange

    have h0 : (1 : k) ⊗ₜ[R] (y : A₁) ∈ Subalgebra.toSubmodule (hopfKer (bc π₁)) :=
      one_tmul_mem_hopfKer_bc π₁ y.2
    rw [← hfield, Subalgebra.map_toSubmodule, ← baseChange_hopfKer_eq (π₁.comp t) (hπ₁.comp ht)] at h0

    have hpush : ((Subalgebra.toSubmodule (hopfKer (π₁.comp t))).baseChange k).map
        (bc (C := A₁) t : k ⊗[R] A₂ →ₐ[k] k ⊗[R] A₁).toLinearMap ≤ T.baseChange k := by
      rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      change (bc (C := A₁) t) ((1 : k) ⊗ₜ[R] x) ∈ (T.baseChange k)
      rw [bc_tmul]
      exact Submodule.tmul_mem_baseChange_of_mem 1 ⟨x, hx, rfl⟩
    have h1 : (1 : k) ⊗ₜ[R] (y : A₁) ∈ T.baseChange k := hpush h0

    have h2 : (r'.baseChange k) ((1 : k) ⊗ₜ[R] (y : A₁)) = (1 : k) ⊗ₜ[R] y := by
      rw [LinearMap.baseChange_tmul, hr']
    rw [← h2]
    have h3 : (T.baseChange k).map (r'.baseChange k) ≤ (T.comap S.subtype).baseChange k := by
      rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      change (r'.baseChange k) ((1 : k) ⊗ₜ[R] z) ∈ _
      rw [LinearMap.baseChange_tmul]
      refine Submodule.tmul_mem_baseChange_of_mem 1 ?_
      change ((r' z : ↥(hopfKer π₁)) : A₁) ∈ T
      rw [show r' z = ⟨z, hTS hz⟩ from hr' ⟨z, hTS hz⟩]
      exact hz
    exact h3 ⟨_, h1, rfl⟩

  have hfg : (⊤ : Submodule R ↥(hopfKer π₁)).FG := Module.finite_def.mp hfin
  have hle := Submodule.le_of_le_smul_of_le_jacobson_bot hfg
    (IsLocalRing.maximalIdeal_le_jacobson ⊥) hNN
  intro y hy
  have : (⟨y, hy⟩ : ↥(hopfKer π₁)) ∈ T.comap S.subtype := hle Submodule.mem_top
  exact this

end Main

end GAMMA2
p2m_reactivate "P2MW.S_PDivisibleGroup_Tower_map_hopfKer_transitionLE_succ_eq.GAMMA2"

end
p2m_reactivate "P2MW.S_PDivisibleGroup_Tower_map_hopfKer_transitionLE_succ_eq.GAMMA2"

theorem solution
    {R : Type} [CommRing R] [IsLocalRing R] (i₀ : ℕ)
    (B : ℕ → Type) [∀ w, CommRing (B w)] [∀ w, HopfAlgebra R (B w)]
    [∀ w, Coalgebra.IsCocomm R (B w)] [∀ w, Module.Finite R (B w)] [∀ w, Module.Free R (B w)]
    (t : ∀ w, B (w + 1) →ₐc[R] B w) (ht : ∀ w, Function.Surjective (t w))
    (hfree : ∀ v, Module.Free R ↥(HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v))) (v : ℕ) :
    (HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ (v + 1))).map
        (t (i₀ + v) : B (i₀ + v + 1) →ₐ[R] B (i₀ + v)) =
      HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v) := by
  haveI : Module.Free R ↥(HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v)) := hfree v
  haveI : Module.Free R ↥(HopfAlgebra.hopfKer
      ((PDivisibleGroup.Tower.transitionLE t i₀ v).comp (t (i₀ + v)))) := hfree (v + 1)
  exact GAMMA2.map_hopfKer_comp_eq (t (i₀ + v)) (PDivisibleGroup.Tower.transitionLE t i₀ v) (ht (i₀ + v))
    (PDivisibleGroup.Tower.transitionLE_surjective t ht i₀ v)

end S_PDivisibleGroup_Tower_map_hopfKer_transitionLE_succ_eq
end P2MW
export P2MW.S_PDivisibleGroup_Tower_map_hopfKer_transitionLE_succ_eq (solution)
