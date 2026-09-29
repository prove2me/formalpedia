-- Prove2me | solution 1 for Rep.isZero_tateCohomology_free_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/b4a7484a-9d39-53aa-8e99-fdc3963fab00

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Theorems.Thm_Rep_indBot_rho_indBotMk
import Theorems.Thm_Rep_nonempty_tateCohomology_iso_of_iso
import Theorems.Thm_Rep_isZero_tateCohomology_indBot
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_isZero_tateCohomology_free_tensor

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace P2mS26K7
p2m_open "Representation TensorProduct Representation.TensorProduct"

variable {k G : Type*} [CommRing k] [Group G]

section model
variable {A : Type*} [AddCommGroup A] [Module k A] (ρ : Representation k (⊥ : Subgroup G) A)

lemma ker_tprod_bot_eq_bot :
    Representation.Coinvariants.ker (V := MonoidAlgebra k G ⊗[k] A)
      (Representation.tprod ((Representation.leftRegular k G).comp (⊥ : Subgroup G).subtype) ρ) = ⊥ := by
  rw [Representation.Coinvariants.ker, Submodule.span_eq_bot]
  rintro _ ⟨⟨g, v⟩, rfl⟩
  have hg : g = 1 := Subsingleton.elim _ _
  simp [hg]

noncomputable def E [DecidableEq G] : (G →₀ A) ≃ₗ[k] Representation.IndV (⊥ : Subgroup G).subtype ρ :=
  (finsuppScalarLeft k A G).symm.trans <|
    ((MonoidAlgebra.coeffLinearEquiv k).rTensor A).symm.trans
      ((Submodule.quotEquivOfEqBot _ (ker_tprod_bot_eq_bot ρ)).symm :
        (MonoidAlgebra k G ⊗[k] A) ≃ₗ[k] Representation.Coinvariants (V := MonoidAlgebra k G ⊗[k] A)
          (Representation.tprod ((Representation.leftRegular k G).comp (⊥ : Subgroup G).subtype) ρ))

lemma E_single [DecidableEq G] (g : G) (a : A) :
    E ρ (Finsupp.single g a) = Representation.IndV.mk (⊥ : Subgroup G).subtype ρ g a := by
  rw [E, LinearEquiv.trans_apply, finsuppScalarLeft_symm_apply_single, LinearEquiv.trans_apply]
  rfl

lemma ind_E [DecidableEq G] (h : G) (f : G →₀ A) :
    Representation.ind (⊥ : Subgroup G).subtype ρ h (E ρ f) = E ρ (Finsupp.lmapDomain A k (fun x => x * h⁻¹) f) := by
  have : (Representation.ind (⊥ : Subgroup G).subtype ρ h) ∘ₗ (E ρ).toLinearMap
      = (E ρ).toLinearMap ∘ₗ Finsupp.lmapDomain A k (fun x => x * h⁻¹) := by
    apply Finsupp.lhom_ext
    intro g a
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    rw [E_single, E_single, ind_mk]
  exact LinearMap.congr_fun this f

end model

section untwist
variable (α : Type*) (M : Rep k G)

lemma rho_self_inv (x : G) (v : M) : M.ρ x (M.ρ x⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

lemma rho_inv_self (x : G) (v : M) : M.ρ x⁻¹ (M.ρ x v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

noncomputable def fwd : ((α →₀ G →₀ k) ⊗[k] M) →ₗ[k] (G →₀ (α →₀ M)) :=
  TensorProduct.lift (Finsupp.lsum k fun a => Finsupp.lsum k fun h =>
    (LinearMap.lsmul k (M →ₗ[k] (G →₀ (α →₀ M)))).flip
      ((Finsupp.lsingle h⁻¹ : (α →₀ M) →ₗ[k] (G →₀ (α →₀ M))) ∘ₗ (Finsupp.lsingle a : M →ₗ[k] (α →₀ M)) ∘ₗ M.ρ h⁻¹))

lemma fwd_tmul (a : α) (h : G) (r : k) (m : M) :
    fwd α M (Finsupp.single a (Finsupp.single h r) ⊗ₜ[k] m)
      = Finsupp.single h⁻¹ (Finsupp.single a (r • M.ρ h⁻¹ m)) := by
  simp only [fwd, TensorProduct.lift.tmul, Finsupp.lsum_single, LinearMap.flip_apply, LinearMap.lsmul_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [← Finsupp.smul_single, ← Finsupp.smul_single]

noncomputable def bwd : (G →₀ (α →₀ M)) →ₗ[k] ((α →₀ G →₀ k) ⊗[k] M) :=
  Finsupp.lsum k fun x => Finsupp.lsum k fun a =>
    (TensorProduct.mk k (α →₀ G →₀ k) M (Finsupp.single a (Finsupp.single x⁻¹ 1))) ∘ₗ M.ρ x⁻¹

lemma bwd_single (x : G) (a : α) (v : M) :
    bwd α M (Finsupp.single x (Finsupp.single a v)) = Finsupp.single a (Finsupp.single x⁻¹ (1 : k)) ⊗ₜ[k] M.ρ x⁻¹ v := by
  simp only [bwd, Finsupp.lsum_single, LinearMap.comp_apply, TensorProduct.mk_apply]

lemma fwd_bwd : fwd α M ∘ₗ bwd α M = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro x f
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Finsupp.single_add, map_add, map_add, hf, hg]
  | single a v =>
    rw [LinearMap.comp_apply, bwd_single, fwd_tmul, LinearMap.id_apply, inv_inv x, one_smul k, rho_self_inv]

lemma bwd_fwd : bwd α M ∘ₗ fwd α M = LinearMap.id := by
  apply TensorProduct.ext'
  intro f m
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [TensorProduct.add_tmul, map_add, map_add, hf, hg]
  | single a q =>
    induction q using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [Finsupp.single_add, TensorProduct.add_tmul, map_add, map_add, hf, hg]
    | single h r =>
      rw [LinearMap.comp_apply, fwd_tmul, bwd_single, LinearMap.id_apply, inv_inv h, map_smul, rho_self_inv,
        ← TensorProduct.smul_tmul, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, mul_one]

noncomputable def U : ((α →₀ G →₀ k) ⊗[k] M) ≃ₗ[k] (G →₀ (α →₀ M)) :=
  LinearEquiv.ofLinear (fwd α M) (bwd α M) (fwd_bwd α M) (bwd_fwd α M)

lemma U_tmul (a : α) (h : G) (r : k) (m : M) :
    U α M (Finsupp.single a (Finsupp.single h r) ⊗ₜ[k] m) = Finsupp.single h⁻¹ (Finsupp.single a (r • M.ρ h⁻¹ m)) :=
  fwd_tmul α M a h r m

end untwist
end P2mS26K7

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (α : Type u) (M : Rep.{u} k G) (q : ℤ) :
    CategoryTheory.Limits.IsZero ((Rep.free k G α ⊗ M).tateCohomology q) := by
  classical

  let T : Rep.{u} k G := Rep.trivial k G (α →₀ M)
  let ρ₀ : Representation k (⊥ : Subgroup G) (α →₀ M) := (Rep.res (⊥ : Subgroup G).subtype T).ρ
  let V : ((Rep.free k G α ⊗ M : Rep k G) : Type u) ≃ₗ[k] TensorProduct k (α →₀ G →₀ k) M :=
    (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv k)).rTensor M
  have hV : ∀ (a : α) (h : G) (r : k) (m : M),
      V (Finsupp.single a (MonoidAlgebra.single h r) ⊗ₜ[k] m) = Finsupp.single a (Finsupp.single h r) ⊗ₜ[k] m :=
    fun a h r m => by
      change (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv k)
          (Finsupp.single a (MonoidAlgebra.single h r))) ⊗ₜ[k] m = _
      rw [Finsupp.mapRange.linearEquiv_apply, Finsupp.mapRange_single]
      rfl
  let Φ : ((Rep.free k G α ⊗ M : Rep k G) : Type u) ≃ₗ[k] T.indBot :=
    V.trans ((P2mS26K7.U α M).trans (P2mS26K7.E (G := G) ρ₀))
  have hΦ : ∀ (a : α) (h : G) (r : k) (m : M),
      Φ (Finsupp.single a (MonoidAlgebra.single h r) ⊗ₜ[k] m) = T.indBotMk h⁻¹ (Finsupp.single a (r • M.ρ h⁻¹ m)) :=
    fun a h r m => by
      change P2mS26K7.E ρ₀ (P2mS26K7.U α M (V (Finsupp.single a (MonoidAlgebra.single h r) ⊗ₜ[k] m))) = _
      rw [hV, P2mS26K7.U_tmul, P2mS26K7.E_single]
      rfl

  have hequiv : ∀ g : G, Φ.toLinearMap ∘ₗ (Rep.free k G α ⊗ M).ρ g = T.indBot.ρ g ∘ₗ Φ.toLinearMap := by
    intro g
    apply TensorProduct.ext'
    intro f m
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f f' hf hf' => rw [TensorProduct.add_tmul, map_add, map_add, hf, hf']
    | single a p =>
      induction p using MonoidAlgebra.induction_linear with
      | zero => simp
      | add p p' hp hp' => rw [Finsupp.single_add, TensorProduct.add_tmul, map_add, map_add, hp, hp']
      | single h r =>
        change Φ ((Rep.free k G α ⊗ M).ρ g (Finsupp.single a (MonoidAlgebra.single h r) ⊗ₜ[k] m))
          = T.indBot.ρ g (Φ (Finsupp.single a (MonoidAlgebra.single h r) ⊗ₜ[k] m))
        rw [Rep.tensor_ρ, Representation.tprod_apply, TensorProduct.map_tmul]
        change Φ (Representation.free k G α g (Finsupp.single a (MonoidAlgebra.single h r)) ⊗ₜ[k] M.ρ g m) = _
        rw [Representation.free_single_single, hΦ, hΦ, Rep.indBot_rho_indBotMk, mul_inv_rev, map_mul, Module.End.mul_apply,
          P2mS26K7.rho_inv_self]
  have hequiv' : ∀ (g : G) x, Φ ((Rep.free k G α ⊗ M).ρ g x) = T.indBot.ρ g (Φ x) := fun g x =>
    LinearMap.congr_fun (hequiv g) x
  have hequiv_symm : ∀ g : G, Φ.symm.toLinearMap ∘ₗ T.indBot.ρ g = (Rep.free k G α ⊗ M).ρ g ∘ₗ Φ.symm.toLinearMap := by
    intro g
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := Φ.surjective y
    change Φ.symm (T.indBot.ρ g (Φ x)) = (Rep.free k G α ⊗ M).ρ g (Φ.symm (Φ x))
    rw [← hequiv', Φ.symm_apply_apply, Φ.symm_apply_apply]
  let e : (Rep.free k G α ⊗ M) ≅ T.indBot :=
    { hom := Rep.ofHom ⟨Φ.toLinearMap, hequiv⟩
      inv := Rep.ofHom ⟨Φ.symm.toLinearMap, hequiv_symm⟩
      hom_inv_id := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => Φ.symm_apply_apply x))
      inv_hom_id := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun y => Φ.apply_symm_apply y)) }
  obtain ⟨f⟩ := Rep.nonempty_tateCohomology_iso_of_iso e q
  exact Limits.IsZero.of_iso (Rep.isZero_tateCohomology_indBot T q) f.symm.symm

end

end S_Rep_isZero_tateCohomology_free_tensor
end P2MW
export P2MW.S_Rep_isZero_tateCohomology_free_tensor (solution)
