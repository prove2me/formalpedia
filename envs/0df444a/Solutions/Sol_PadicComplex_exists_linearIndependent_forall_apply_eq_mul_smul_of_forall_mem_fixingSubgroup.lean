-- Prove2me | solution 1 for PadicComplex.exists_linearIndependent_forall_apply_eq_mul_smul_of_forall_mem_fixingSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c265ac2e-289e-57ff-a7e1-7e900067c97c

import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Theorems.Thm_IsGalois_exists_basis_baseChange_forall_apply_eq_self
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicComplex_exists_linearIndependent_forall_apply_eq_mul_smul_of_forall_mem_fixingSubgroup

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace HTPOTDESC

variable (p : ℕ) [Fact p.Prime]

local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

variable (W : Type*) [AddCommGroup W] [Module ℂ_[p] W]

structure Datum where

  ρ : Γ → W →+ W
  hρ : ∀ (σ : Γ) (c : ℂ_[p]) (w : W), ρ σ (c • w) = (σ • c) • ρ σ w
  hρone : ∀ w : W, ρ 1 w = w
  hρmul : ∀ (σ τ : Γ) (w : W), ρ (σ * τ) w = ρ σ (ρ τ w)

  χ : Γ →* ℂ_[p]ˣ
  hχ : ∀ σ τ : Γ, σ • ((χ τ : ℂ_[p]ˣ) : ℂ_[p]) = χ τ

variable {W} (D : Datum p W)

def star (σ : Γ) (φ : W →ₗ[ℂ_[p]] ℂ_[p]) : W →ₗ[ℂ_[p]] ℂ_[p] where
  toFun x := (D.χ σ : ℂ_[p]) * σ • φ (D.ρ σ⁻¹ x)
  map_add' x y := by
    simp only [map_add, smul_add, mul_add]
  map_smul' c x := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [D.hρ, map_smul, smul_eq_mul, smul_mul', smul_inv_smul]
    ring

theorem star_apply (σ : Γ) (φ : W →ₗ[ℂ_[p]] ℂ_[p]) (x : W) :
    star p D σ φ x = (D.χ σ : ℂ_[p]) * σ • φ (D.ρ σ⁻¹ x) := rfl

theorem star_add (σ : Γ) (φ ψ : W →ₗ[ℂ_[p]] ℂ_[p]) :
    star p D σ (φ + ψ) = star p D σ φ + star p D σ ψ := by
  refine LinearMap.ext fun x => ?_
  simp only [star_apply, LinearMap.add_apply, smul_add, mul_add]

theorem star_zero (σ : Γ) : star p D σ (0 : W →ₗ[ℂ_[p]] ℂ_[p]) = 0 := by
  refine LinearMap.ext fun x => ?_
  simp only [star_apply, LinearMap.zero_apply, smul_zero, mul_zero]

theorem star_smul (σ : Γ) (c : ℂ_[p]) (φ : W →ₗ[ℂ_[p]] ℂ_[p]) :
    star p D σ (c • φ) = (σ • c) • star p D σ φ := by
  refine LinearMap.ext fun x => ?_
  simp only [star_apply, LinearMap.smul_apply, smul_eq_mul, smul_mul']
  ring

theorem star_one (φ : W →ₗ[ℂ_[p]] ℂ_[p]) : star p D 1 φ = φ := by
  refine LinearMap.ext fun x => ?_
  rw [star_apply, map_one, Units.val_one, one_mul, one_smul, inv_one, D.hρone]

theorem star_mul (σ τ : Γ) (φ : W →ₗ[ℂ_[p]] ℂ_[p]) :
    star p D (σ * τ) φ = star p D σ (star p D τ φ) := by
  refine LinearMap.ext fun x => ?_
  simp only [star_apply]
  rw [mul_inv_rev, D.hρmul, map_mul, Units.val_mul, mul_smul, smul_mul', D.hχ]
  ring

theorem star_eq_self_of_equivariant (H : Subgroup Γ) (φ : W →ₗ[ℂ_[p]] ℂ_[p])
    (hφ : ∀ τ : Γ, τ ∈ H → ∀ x : W, φ (D.ρ τ x) = (D.χ τ : ℂ_[p]) * τ • φ x)
    (τ : Γ) (hτ : τ ∈ H) : star p D τ φ = φ := by
  refine LinearMap.ext fun x => ?_
  rw [star_apply, hφ τ⁻¹ (H.inv_mem hτ), smul_mul', D.hχ, smul_inv_smul, ← mul_assoc,
    ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mul]

theorem equivariant_of_star_eq_self (φ : W →ₗ[ℂ_[p]] ℂ_[p])
    (hφ : ∀ σ : Γ, star p D σ φ = φ) (σ : Γ) (x : W) :
    φ (D.ρ σ x) = (D.χ σ : ℂ_[p]) * σ • φ x := by
  conv_lhs => rw [← hφ σ]
  rw [star_apply, ← D.hρmul, inv_mul_cancel, D.hρone]

section Normal

variable (E : IntermediateField ℚ_[p] (PadicAlgCl p))

section res

variable [Normal ℚ_[p] E]

def res : Γ →* (E ≃ₐ[ℚ_[p]] E) := AlgEquiv.restrictNormalHom E

theorem res_spec (σ : Γ) (x : E) : ((res p E σ x : E) : PadicAlgCl p) = σ (x : PadicAlgCl p) := by
  unfold res
  exact AlgEquiv.restrictNormal_commutes σ E x

theorem res_surjective : Function.Surjective (res p E) := by
  unfold res
  exact AlgEquiv.restrictNormalHom_surjective (F := ℚ_[p]) (K₁ := E) (PadicAlgCl p)

theorem mem_fixingSubgroup_of_res_eq {σ τ : Γ} (h : res p E σ = res p E τ) :
    τ⁻¹ * σ ∈ E.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have h1 : σ x = τ x := by
    have := congrArg (fun δ : E ≃ₐ[ℚ_[p]] E => ((δ ⟨x, hx⟩ : E) : PadicAlgCl p)) h
    simp only [res_spec] at this
    exact this
  rw [AlgEquiv.mul_apply, h1]
  exact τ.symm_apply_apply x

theorem conj_mem_fixingSubgroup {τ : Γ} (hτ : τ ∈ E.fixingSubgroup) (σ : Γ) :
    σ⁻¹ * τ * σ ∈ E.fixingSubgroup := by
  rw [← IntermediateField.restrictNormalHom_ker] at hτ ⊢
  rw [MonoidHom.mem_ker] at hτ ⊢
  rw [map_mul, map_mul, hτ, mul_one, ← map_mul, inv_mul_cancel, map_one]

private def _root_.HTPOTDESC.lift (q : E ≃ₐ[ℚ_[p]] E) : Γ := Function.surjInv (res_surjective p E) q

p2m_export "HTPOTDESC" "lift"
theorem res_lift (q : E ≃ₐ[ℚ_[p]] E) : res p E (lift p E q) = q :=
  Function.surjInv_eq (res_surjective p E) q

theorem smul_coe_coe (σ : Γ) (a : E) :
    σ • (((a : PadicAlgCl p) : ℂ_[p])) = (((res p E σ a : E) : PadicAlgCl p) : ℂ_[p]) := by
  rw [PadicComplex.smul_coe, res_spec]

end res

theorem smul_coe_coe_of_mem {τ : Γ} (hτ : τ ∈ E.fixingSubgroup) (a : E) :
    τ • (((a : PadicAlgCl p) : ℂ_[p])) = ((a : PadicAlgCl p) : ℂ_[p]) := by
  rw [PadicComplex.smul_coe, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ _ a.2]

structure IsFixed (φ : W →ₗ[ℂ_[p]] ℂ_[p]) : Prop where
  out : ∀ τ : Γ, τ ∈ E.fixingSubgroup → star p D τ φ = φ

theorem isFixed_zero : IsFixed p D E 0 := ⟨fun τ _ => star_zero p D τ⟩

variable {p D E} in
theorem IsFixed.add {φ ψ : W →ₗ[ℂ_[p]] ℂ_[p]} (hφ : IsFixed p D E φ) (hψ : IsFixed p D E ψ) :
    IsFixed p D E (φ + ψ) := ⟨fun τ hτ => by rw [star_add, hφ.out τ hτ, hψ.out τ hτ]⟩

variable {p D E} in
theorem IsFixed.smul_rat (c : ℚ_[p]) {φ : W →ₗ[ℂ_[p]] ℂ_[p]} (hφ : IsFixed p D E φ) :
    IsFixed p D E (c • φ) := ⟨fun τ hτ => by
  rw [← algebraMap_smul ℂ_[p] c φ, star_smul, PadicComplex.smul_algebraMap, hφ.out τ hτ]⟩

def emb : E →ₐ[ℚ_[p]] ℂ_[p] := (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).comp E.val

theorem emb_apply (a : E) : emb p E a = ((a : PadicAlgCl p) : ℂ_[p]) := rfl

theorem emb_smul (c : ℚ_[p]) (a : E) : emb p E (c • a) = c • emb p E a := by
  rw [Algebra.smul_def, map_mul, AlgHom.commutes, ← Algebra.smul_def]

variable {p D E} in
theorem IsFixed.smul_emb (a : E) {φ : W →ₗ[ℂ_[p]] ℂ_[p]} (hφ : IsFixed p D E φ) :
    IsFixed p D E (emb p E a • φ) := ⟨fun τ hτ => by
  rw [star_smul, emb_apply, smul_coe_coe_of_mem p E hτ, hφ.out τ hτ]⟩

variable [Normal ℚ_[p] E]

theorem isFixed_star (σ : Γ) {φ : W →ₗ[ℂ_[p]] ℂ_[p]} (hφ : IsFixed p D E φ) :
    IsFixed p D E (star p D σ φ) := by
  refine ⟨fun τ hτ => ?_⟩
  have hconj := hφ.out _ (conj_mem_fixingSubgroup p E hτ σ)
  rw [← star_mul]
  conv_lhs => rw [show τ * σ = σ * (σ⁻¹ * τ * σ) by group]
  rw [star_mul, hconj]

variable {p D E} in

theorem IsFixed.star_eq_star_of_res_eq {σ σ' : Γ} (h : res p E σ = res p E σ')
    {φ : W →ₗ[ℂ_[p]] ℂ_[p]} (hφ : IsFixed p D E φ) :
    HTPOTDESC.star p D σ φ = HTPOTDESC.star p D σ' φ := by
  have hmem := mem_fixingSubgroup_of_res_eq p E h
  conv_lhs => rw [show σ = σ' * (σ'⁻¹ * σ) by group]
  rw [star_mul, hφ.out _ hmem]

private theorem _root_.HTPOTDESC.smul_emb (σ : Γ) (a : E) : σ • emb p E a = emb p E (res p E σ a) := by
  rw [emb_apply, emb_apply, smul_coe_coe]

p2m_export "HTPOTDESC" "smul_emb"
variable [FiniteDimensional ℚ_[p] E]

variable {ι : Type*} (f : ι → (W →ₗ[ℂ_[p]] ℂ_[p]))

def bE : Module.Basis (Fin (Module.finrank ℚ_[p] E)) ℚ_[p] E := Module.finBasis ℚ_[p] E

def gen (t : Fin (Module.finrank ℚ_[p] E) × (E ≃ₐ[ℚ_[p]] E) × ι) : W →ₗ[ℂ_[p]] ℂ_[p] :=
  emb p E (bE p E t.1) • star p D (lift p E t.2.1) (f t.2.2)

def orbitSpan : Submodule ℚ_[p] (W →ₗ[ℂ_[p]] ℂ_[p]) :=
  Submodule.span ℚ_[p] (Set.range (gen p D E f))

scoped instance finiteDimensional_orbitSpan [Finite ι] : FiniteDimensional ℚ_[p] (orbitSpan p D E f) :=
  FiniteDimensional.span_of_finite ℚ_[p] (Set.finite_range _)

scoped instance instModuleLeft : Module E (E ⊗[ℚ_[p]] orbitSpan p D E f) := TensorProduct.leftModule

scoped instance instSMulLeft : SMul E (E ⊗[ℚ_[p]] orbitSpan p D E f) := TensorProduct.leftHasSMul

scoped instance instDistribMulActionLeft : DistribMulAction E (E ⊗[ℚ_[p]] orbitSpan p D E f) :=
  TensorProduct.leftDistribMulAction

scoped instance instSMulZeroClassLeft : SMulZeroClass E (E ⊗[ℚ_[p]] orbitSpan p D E f) :=
  (TensorProduct.leftDistribMulAction).toDistribSMul.toSMulZeroClass

scoped instance instDistribSMulLeft : DistribSMul E (E ⊗[ℚ_[p]] orbitSpan p D E f) :=
  (TensorProduct.leftDistribMulAction).toDistribSMul

omit [Normal ℚ_[p] E] in

theorem emb_eq_sum (a : E) :
    emb p E a = ∑ k, (bE p E).repr a k • emb p E (bE p E k) := by
  conv_lhs => rw [← (bE p E).sum_repr a]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [emb_smul]

theorem emb_smul_mem (a : E) {ψ : W →ₗ[ℂ_[p]] ℂ_[p]} (hψ : ψ ∈ orbitSpan p D E f) :
    emb p E a • ψ ∈ orbitSpan p D E f := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨j, q, i⟩, rfl⟩ := hx
      show emb p E a • (emb p E (bE p E j) • star p D (lift p E q) (f i)) ∈ _
      rw [smul_smul, ← map_mul, emb_eq_sum, Finset.sum_smul]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [smul_assoc]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨k, q, i⟩, rfl⟩)
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

variable (hfE : ∀ i, IsFixed p D E (f i))

include hfE in
theorem isFixed_of_mem {ψ : W →ₗ[ℂ_[p]] ℂ_[p]} (hψ : ψ ∈ orbitSpan p D E f) : IsFixed p D E ψ := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨j, q, i⟩, rfl⟩ := hx
      exact (isFixed_star p D E _ (hfE i)).smul_emb _
  | zero => exact isFixed_zero p D E
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul_rat c

theorem star_lift_mem (q : E ≃ₐ[ℚ_[p]] E) (i : ι) : star p D (lift p E q) (f i) ∈ orbitSpan p D E f := by

  have h1 : star p D (lift p E q) (f i) = emb p E 1 • star p D (lift p E q) (f i) := by
    rw [map_one, one_smul]
  rw [h1, emb_eq_sum, Finset.sum_smul]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [smul_assoc]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨k, q, i⟩, rfl⟩)

include hfE in
theorem mem_orbitSpan (i : ι) : f i ∈ orbitSpan p D E f := by
  have h := star_lift_mem p D E f 1 i
  rwa [(hfE i).star_eq_star_of_res_eq (σ := lift p E 1) (σ' := 1) (by rw [res_lift, map_one]),
    star_one] at h

include hfE in

theorem star_mem_orbitSpan (σ : Γ) {φ : W →ₗ[ℂ_[p]] ℂ_[p]} (hφ : φ ∈ orbitSpan p D E f) :
    star p D σ φ ∈ orbitSpan p D E f := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨j, q, i⟩, rfl⟩ := hx
      show star p D σ (emb p E (bE p E j) • star p D (lift p E q) (f i)) ∈ _
      rw [star_smul, smul_emb, ← star_mul,
        (hfE i).star_eq_star_of_res_eq (σ := σ * lift p E q) (σ' := lift p E (res p E σ * q))
          (by rw [res_lift, map_mul, res_lift])]
      exact emb_smul_mem p D E f _ (star_lift_mem p D E f _ i)
  | zero => rw [star_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
      rw [← algebraMap_smul ℂ_[p] c x, star_smul, PadicComplex.smul_algebraMap, algebraMap_smul]
      exact Submodule.smul_mem _ _ hx

def ρU (q : E ≃ₐ[ℚ_[p]] E) : orbitSpan p D E f →ₗ[ℚ_[p]] orbitSpan p D E f where
  toFun φ := ⟨star p D (lift p E q) φ, star_mem_orbitSpan p D E f hfE _ φ.2⟩
  map_add' φ ψ := by
    ext1
    exact star_add p D _ _ _
  map_smul' c φ := by
    ext1
    show star p D (lift p E q) (c • (φ : W →ₗ[ℂ_[p]] ℂ_[p])) =
      c • star p D (lift p E q) (φ : W →ₗ[ℂ_[p]] ℂ_[p])
    rw [← algebraMap_smul ℂ_[p] c, star_smul, PadicComplex.smul_algebraMap, algebraMap_smul]

theorem coe_ρU (q : E ≃ₐ[ℚ_[p]] E) (φ : orbitSpan p D E f) :
    ((ρU p D E f hfE q φ : orbitSpan p D E f) : W →ₗ[ℂ_[p]] ℂ_[p]) = star p D (lift p E q) φ := rfl

def ρUHom : (E ≃ₐ[ℚ_[p]] E) →* (orbitSpan p D E f →ₗ[ℚ_[p]] orbitSpan p D E f) where
  toFun := ρU p D E f hfE
  map_one' := by
    refine LinearMap.ext fun φ => Subtype.ext ?_
    rw [coe_ρU, Module.End.one_apply,
      (isFixed_of_mem p D E f hfE φ.2).star_eq_star_of_res_eq (σ := lift p E 1) (σ' := 1)
        (by rw [res_lift, map_one]), star_one]
  map_mul' q q' := by
    refine LinearMap.ext fun φ => Subtype.ext ?_
    rw [coe_ρU, Module.End.mul_apply, coe_ρU, coe_ρU, ← star_mul]
    exact (isFixed_of_mem p D E f hfE φ.2).star_eq_star_of_res_eq (σ := lift p E (q * q'))
      (σ' := lift p E q * lift p E q') (by rw [res_lift, map_mul, res_lift, res_lift])

theorem ρUHom_apply (q : E ≃ₐ[ℚ_[p]] E) : ρUHom p D E f hfE q = ρU p D E f hfE q := rfl

def fT (q : E ≃ₐ[ℚ_[p]] E) : E ⊗[ℚ_[p]] orbitSpan p D E f →+ E ⊗[ℚ_[p]] orbitSpan p D E f :=
  (TensorProduct.map (q : E ≃ₐ[ℚ_[p]] E).toLinearMap (ρUHom p D E f hfE q)).toAddMonoidHom

theorem fT_tmul (q : E ≃ₐ[ℚ_[p]] E) (a : E) (φ : orbitSpan p D E f) :
    fT p D E f hfE q (a ⊗ₜ[ℚ_[p]] φ) = q a ⊗ₜ[ℚ_[p]] ρUHom p D E f hfE q φ := rfl

def mult : E ⊗[ℚ_[p]] orbitSpan p D E f →ₗ[ℚ_[p]] (W →ₗ[ℂ_[p]] ℂ_[p]) :=
  TensorProduct.lift (LinearMap.mk₂ ℚ_[p]
    (fun (a : E) (φ : orbitSpan p D E f) => emb p E a • (φ : W →ₗ[ℂ_[p]] ℂ_[p]))
    (fun a a' φ => by simp only [map_add, add_smul])
    (fun c a φ => by simp only [emb_smul, smul_assoc])
    (fun a φ ψ => by simp only [Submodule.coe_add, smul_add])
    (fun c a φ => by simp only [Submodule.coe_smul]; rw [smul_comm]))

theorem mult_tmul (a : E) (φ : orbitSpan p D E f) :
    mult p D E f (a ⊗ₜ[ℚ_[p]] φ) = emb p E a • (φ : W →ₗ[ℂ_[p]] ℂ_[p]) :=
  TensorProduct.lift.tmul _ _

theorem mult_smul (c : E) (z : E ⊗[ℚ_[p]] orbitSpan p D E f) :
    mult p D E f (c • z) = emb p E c • mult p D E f z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul a φ => rw [TensorProduct.smul_tmul', mult_tmul, mult_tmul, smul_eq_mul, map_mul, mul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]

theorem star_mult (σ : Γ) (z : E ⊗[ℚ_[p]] orbitSpan p D E f) :
    star p D σ (mult p D E f z) = mult p D E f (fT p D E f hfE (res p E σ) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, star_zero]
  | tmul a φ =>
      rw [fT_tmul, mult_tmul, mult_tmul, star_smul, smul_emb, ρUHom_apply, coe_ρU]
      congr 1
      exact (isFixed_of_mem p D E f hfE φ.2).star_eq_star_of_res_eq (σ := σ)
        (σ' := lift p E (res p E σ)) (by rw [res_lift])
  | add x y hx hy => rw [map_add, map_add, map_add, star_add, hx, hy]

end Normal

end HTPOTDESC
p2m_reactivate "P2MW.S_PadicComplex_exists_linearIndependent_forall_apply_eq_mul_smul_of_forall_mem_fixingSubgroup.HTPOTDESC"

theorem solution
    (p : ℕ) [Fact p.Prime] {W : Type*} [AddCommGroup W] [Module ℂ_[p] W]
    (ρ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → W →+ W)
    (hρ : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (c : ℂ_[p]) (w : W),
      ρ σ (c • w) = (σ • c) • ρ σ w)
    (hρone : ∀ w : W, ρ 1 w = w)
    (hρmul : ∀ (σ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (w : W), ρ (σ * τ) w = ρ σ (ρ τ w))
    (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* ℂ_[p]ˣ)
    (hχ : ∀ σ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ • ((χ τ : ℂ_[p]ˣ) : ℂ_[p]) = χ τ)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {ι : Type*} [Finite ι] (f : ι → (W →ₗ[ℂ_[p]] ℂ_[p])) (hf : LinearIndependent ℂ_[p] f)
    (hfK : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup →
      ∀ (i : ι) (x : W), f i (ρ σ x) = (χ σ : ℂ_[p]) * σ • f i x) :
    ∃ f' : ι → (W →ₗ[ℂ_[p]] ℂ_[p]), LinearIndependent ℂ_[p] f' ∧
      ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (i : ι) (x : W),
        f' i (ρ σ x) = (χ σ : ℂ_[p]) * σ • f' i x := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  let D : HTPOTDESC.Datum p W := ⟨ρ, hρ, hρone, hρmul, χ, hχ⟩

  let E : IntermediateField ℚ_[p] (PadicAlgCl p) := IntermediateField.normalClosure ℚ_[p] K (PadicAlgCl p)
  haveI : FiniteDimensional ℚ_[p] E := inferInstance
  haveI : IsGalois ℚ_[p] E := inferInstance
  have hle : K ≤ E := IntermediateField.le_normalClosure K

  have hfE : ∀ i, HTPOTDESC.IsFixed p D E (f i) := fun i => ⟨fun τ hτ =>
    HTPOTDESC.star_eq_self_of_equivariant p D K.fixingSubgroup (f i)
      (fun τ hτ x => hfK τ hτ i x) τ (IntermediateField.fixingSubgroup_antitone hle hτ)⟩

  obtain ⟨B, hB⟩ := IsGalois.exists_basis_baseChange_forall_apply_eq_self (K := ℚ_[p]) (L := E)
    (U := HTPOTDESC.orbitSpan p D E f)
    (HTPOTDESC.ρUHom p D E f hfE) (HTPOTDESC.fT p D E f hfE) (HTPOTDESC.fT_tmul p D E f hfE)

  let ψ : Fin (Module.finrank ℚ_[p] (HTPOTDESC.orbitSpan p D E f)) → (W →ₗ[ℂ_[p]] ℂ_[p]) :=
    fun k => HTPOTDESC.mult p D E f (B k)
  have hψfix : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) k, HTPOTDESC.star p D σ (ψ k) = ψ k := by
    intro σ k
    show HTPOTDESC.star p D σ (HTPOTDESC.mult p D E f (B k)) = HTPOTDESC.mult p D E f (B k)
    rw [HTPOTDESC.star_mult p D E f hfE, hB]
  have hψeq : ∀ k (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : W),
      ψ k (ρ σ x) = (χ σ : ℂ_[p]) * σ • ψ k x := fun k =>
    HTPOTDESC.equivariant_of_star_eq_self p D (ψ k) (fun σ => hψfix σ k)

  have hmemC : ∀ i, f i ∈ Submodule.span ℂ_[p] (Set.range ψ) := by
    intro i
    let u : HTPOTDESC.orbitSpan p D E f := ⟨f i, HTPOTDESC.mem_orbitSpan p D E f hfE i⟩
    have h1 : f i = HTPOTDESC.mult p D E f ((1 : E) ⊗ₜ[ℚ_[p]] u) := by
      rw [HTPOTDESC.mult_tmul, map_one, one_smul]
    have h2 : (1 : E) ⊗ₜ[ℚ_[p]] u = ∑ k, (B.repr ((1 : E) ⊗ₜ[ℚ_[p]] u) k) • B k :=
      (B.sum_repr _).symm
    rw [h1, h2, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [HTPOTDESC.mult_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

  set S : Submodule ℂ_[p] (W →ₗ[ℂ_[p]] ℂ_[p]) := Submodule.span ℂ_[p] (Set.range ψ) with hS
  haveI : FiniteDimensional ℂ_[p] S := FiniteDimensional.span_of_finite ℂ_[p] (Set.finite_range ψ)
  have hcard : Fintype.card ι ≤ Module.finrank ℂ_[p] S := by
    let g : ι → S := fun i => ⟨f i, hmemC i⟩
    have hg : LinearIndependent ℂ_[p] g :=
      LinearIndependent.of_comp S.subtype (by exact hf)
    exact hg.fintype_card_le_finrank
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent ℂ_[p] (Set.range ψ)
  have hbfin : b.Finite := (Set.finite_range ψ).subset hbsub
  letI : Fintype b := hbfin.fintype
  have hcardb : Module.finrank ℂ_[p] S = b.toFinset.card := by
    rw [hS, ← hbspan]
    exact finrank_span_set_eq_card hbli
  have hle' : Fintype.card ι ≤ b.toFinset.card := hcardb ▸ hcard
  obtain ⟨emb, hemb⟩ := Function.Embedding.exists_of_card_le_finset hle'
  have hmemb : ∀ i, emb i ∈ b := fun i => by
    have := hemb ⟨i, rfl⟩
    simpa only [Set.coe_toFinset] using this
  refine ⟨fun i => emb i, ?_, fun σ i x => ?_⟩
  ·
    exact hbli.comp (fun i => ⟨emb i, hmemb i⟩) fun i j hij =>
      emb.injective (congrArg Subtype.val hij)
  ·
    obtain ⟨k, hk⟩ := hbsub (hmemb i)
    change (emb i) (ρ σ x) = (χ σ : ℂ_[p]) * σ • (emb i) x
    rw [← hk]
    exact hψeq k σ x

end
p2m_reactivate "P2MW.S_PadicComplex_exists_linearIndependent_forall_apply_eq_mul_smul_of_forall_mem_fixingSubgroup.HTPOTDESC"

end S_PadicComplex_exists_linearIndependent_forall_apply_eq_mul_smul_of_forall_mem_fixingSubgroup
end P2MW
export P2MW.S_PadicComplex_exists_linearIndependent_forall_apply_eq_mul_smul_of_forall_mem_fixingSubgroup (solution)
