-- Prove2me | solution 1 for Rep.nonempty_ind_res_iso_tensor_ofMulAction_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/97abacd6-f081-52a6-b836-165a165cbb08

import Mathlib
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_nonempty_ind_res_iso_tensor_ofMulAction_quotient
set_option maxHeartbeats 200000

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module"
open scoped Classical

set_option linter.unusedSimpArgs false

namespace PermInd

open Representation

variable {k : Type} [CommRing k] {G : Type} [Group G] (D : Subgroup G) (M : Rep.{0} k G)

lemma rho_inv_self (g : G) (m : M) : M.ρ g⁻¹ (M.ρ g m) = m := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

lemma rho_self_inv (g : G) (m : M) : M.ρ g (M.ρ g⁻¹ m) = m := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

abbrev ρD : Representation k D M := M.ρ.comp D.subtype

noncomputable def fwdAux : TensorProduct k (MonoidAlgebra k G) M →ₗ[k] TensorProduct k M ((G ⧸ D) →₀ k) :=
  TensorProduct.lift ((Finsupp.lift (M →ₗ[k] TensorProduct k M ((G ⧸ D) →₀ k)) k G fun g =>
    (TensorProduct.mk k M ((G ⧸ D) →₀ k)).flip (Finsupp.single ((g⁻¹ : G) : G ⧸ D) 1) ∘ₗ M.ρ g⁻¹) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)

@[scoped simp]
lemma fwdAux_single_tmul (g : G) (r : k) (m : M) :
    fwdAux D M (MonoidAlgebra.single g r ⊗ₜ m) =
      r • (M.ρ g⁻¹ m ⊗ₜ Finsupp.single ((g⁻¹ : G) : G ⧸ D) (1 : k)) := by
  simp [fwdAux]

noncomputable def fwd : IndV D.subtype (ρD D M) →ₗ[k] TensorProduct k M ((G ⧸ D) →₀ k) :=
  Coinvariants.lift _ (fwdAux D M) fun d => by
    refine TensorProduct.ext ?_
    refine MonoidAlgebra.lhom_ext' fun g => LinearMap.ext_ring (LinearMap.ext fun m => ?_)
    have hq : (((g⁻¹ * (d : G)⁻¹ : G)) : G ⧸ D) = ((g⁻¹ : G) : G ⧸ D) := by
      rw [QuotientGroup.eq]; simp
    simp [Representation.tprod_apply, mul_inv_rev, rho_inv_self, hq]

@[scoped simp]
lemma fwd_mk_single_tmul (g : G) (r : k) (m : M) :
    fwd D M (Coinvariants.mk _ (MonoidAlgebra.single g r ⊗ₜ m)) =
      r • (M.ρ g⁻¹ m ⊗ₜ Finsupp.single ((g⁻¹ : G) : G ⧸ D) (1 : k)) := by
  simp [fwd]

lemma fwd_indVMk (g : G) (m : M) :
    fwd D M (IndV.mk D.subtype (ρD D M) g m) =
      M.ρ g⁻¹ m ⊗ₜ Finsupp.single ((g⁻¹ : G) : G ⧸ D) (1 : k) := by
  simp [IndV.mk]

noncomputable def bwdFun (q : G ⧸ D) : M →ₗ[k] IndV D.subtype (ρD D M) :=
  Quotient.liftOn' q (fun g : G => IndV.mk D.subtype (ρD D M) g⁻¹ ∘ₗ M.ρ g⁻¹) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab
    refine LinearMap.ext fun m => ?_

    have key := Coinvariants.mk_self_apply
      (tprod ((leftRegular k G).comp D.subtype) (ρD D M)) ⟨(a⁻¹ * b)⁻¹, D.inv_mem hab⟩
      (MonoidAlgebra.single a⁻¹ (1 : k) ⊗ₜ M.ρ a⁻¹ m)
    simp only [Representation.tprod_apply, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype, TensorProduct.map_tmul, ofMulAction_single, smul_eq_mul] at key
    simp only [LinearMap.coe_comp, Function.comp_apply]
    show Coinvariants.mk _ (MonoidAlgebra.single a⁻¹ (1 : k) ⊗ₜ M.ρ a⁻¹ m) =
      Coinvariants.mk _ (MonoidAlgebra.single b⁻¹ (1 : k) ⊗ₜ M.ρ b⁻¹ m)
    rw [← key, ← Module.End.mul_apply, ← map_mul]
    congr 3
    · group
    · group

@[scoped simp]
lemma bwdFun_mk (g : G) (m : M) :
    bwdFun D M (g : G ⧸ D) m = IndV.mk D.subtype (ρD D M) g⁻¹ (M.ρ g⁻¹ m) := rfl

noncomputable def bwd : TensorProduct k M ((G ⧸ D) →₀ k) →ₗ[k] IndV D.subtype (ρD D M) :=
  TensorProduct.lift (Finsupp.lift (M →ₗ[k] IndV D.subtype (ρD D M)) k (G ⧸ D) (bwdFun D M)) ∘ₗ
    (TensorProduct.comm k M ((G ⧸ D) →₀ k)).toLinearMap

@[scoped simp]
lemma bwd_tmul_single (m : M) (g : G) (r : k) :
    bwd D M (m ⊗ₜ Finsupp.single (g : G ⧸ D) r) =
      r • IndV.mk D.subtype (ρD D M) g⁻¹ (M.ρ g⁻¹ m) := by
  simp [bwd]

lemma bwd_fwd : bwd D M ∘ₗ fwd D M = LinearMap.id := by
  refine IndV.hom_ext _ _ fun g => LinearMap.ext fun m => ?_
  simp [rho_self_inv]

lemma fwd_bwd : fwd D M ∘ₗ bwd D M = LinearMap.id := by
  refine TensorProduct.ext' fun m f => ?_
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => simp_all [TensorProduct.tmul_add]
  | single q r =>
    induction q using QuotientGroup.induction_on with
    | H g =>
      simp [rho_self_inv]
      rw [← TensorProduct.tmul_smul, Finsupp.smul_single_one]

noncomputable def lequiv : IndV D.subtype (ρD D M) ≃ₗ[k] TensorProduct k M ((G ⧸ D) →₀ k) :=
  LinearEquiv.ofLinear (fwd D M) (bwd D M) (fwd_bwd D M) (bwd_fwd D M)

lemma fwd_equivariant (h : G) :
    (lequiv D M).toLinearMap ∘ₗ (ind D.subtype (ρD D M)) h =
      (M.ρ.tprod (ofMulActionFinsupp k G (G ⧸ D))) h ∘ₗ (lequiv D M).toLinearMap := by
  refine IndV.hom_ext _ _ fun g => LinearMap.ext fun m => ?_
  simp [lequiv, Representation.tprod_apply, ind_mk, mul_inv_rev, MulAction.Quotient.smul_mk]

noncomputable def iso : Rep.ind D.subtype (Rep.res D.subtype M) ≅ M ⊗ Rep.ofMulActionFinsupp k G (G ⧸ D) :=
  Rep.mkIso (Representation.Equiv.mk (lequiv D M) (fwd_equivariant D M))

end PermInd
p2m_reactivate "P2MW.S_Rep_nonempty_ind_res_iso_tensor_ofMulAction_quotient.PermInd"

theorem solution
    {k : Type} [CommRing k] {G : Type} [Group G] (D : Subgroup G) (M : Rep.{0} k G) :
    Nonempty (Rep.ind D.subtype (Rep.res D.subtype M) ≅ M ⊗ Rep.ofMulActionFinsupp k G (G ⧸ D)) :=
  ⟨PermInd.iso D M⟩

end S_Rep_nonempty_ind_res_iso_tensor_ofMulAction_quotient
end P2MW
export P2MW.S_Rep_nonempty_ind_res_iso_tensor_ofMulAction_quotient (solution)
