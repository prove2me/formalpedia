-- Prove2me | solution 1 for Rep.isZero_tateCohomology_ihom_indBot_trivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/3b69a321-3468-5c15-9f39-4263e218d9ee

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Theorems.Thm_Rep_nonempty_tateCohomology_iso_of_iso
import Theorems.Thm_Rep_isZero_tateCohomology_indBot
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_isZero_tateCohomology_ihom_indBot_trivial

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace P2mS26K3
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

private lemma _root_.P2mS26K3.lmapDomain_apply (h : G) (f : G →₀ A) (y : G) :
    Finsupp.lmapDomain A k (fun x => x * h⁻¹) f y = f (y * h) := by
  rw [Finsupp.lmapDomain_apply]
  conv_lhs => rw [← mul_inv_cancel_right y h]
  exact Finsupp.mapDomain_apply (mul_left_injective h⁻¹) f (y * h)

p2m_export "P2mS26K3" "lmapDomain_apply"
end model
end P2mS26K3

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (M : ModuleCat.{u} k) (W : Rep.{u} k G) (q : ℤ) :
    CategoryTheory.Limits.IsZero (((ihom (Rep.trivial k G M).indBot).obj W).tateCohomology q) := by
  classical

  let T : Rep.{u} k G := Rep.trivial k G M
  let ρ₀ : Representation k (⊥ : Subgroup G) M := (Rep.res (⊥ : Subgroup G).subtype T).ρ
  let I : Rep.{u} k G := T.indBot
  let EM : (G →₀ M) ≃ₗ[k] I := P2mS26K3.E (G := G) ρ₀
  let A : Rep.{u} k G := (ihom I).obj W
  let ofA : A → (I →ₗ[k] W) := fun φ => φ
  let toA : (I →ₗ[k] W) → A := fun φ => φ
  have hAρ : ∀ (g : G) (φ : A), ofA (A.ρ g φ) = W.ρ g ∘ₗ ofA φ ∘ₗ I.ρ g⁻¹ := fun g φ => Rep.ihom_obj_ρ_apply g (ofA φ)
  let V : Type u := M →ₗ[k] W
  let TV : Rep.{u} k G := Rep.trivial k G V
  let σ₀ : Representation k (⊥ : Subgroup G) V := (Rep.res (⊥ : Subgroup G).subtype TV).ρ
  let J : Rep.{u} k G := TV.indBot
  let EV : (G →₀ V) ≃ₗ[k] J := P2mS26K3.E (G := G) σ₀
  have ρWinv : ∀ (x : G) (w : W), W.ρ x (W.ρ x⁻¹ w) = w := fun x w => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have ρWinv' : ∀ (x : G) (w : W), W.ρ x⁻¹ (W.ρ x w) = w := fun x w => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

  have hIρ : ∀ (g x : G) (m : M), I.ρ g (EM (Finsupp.single x m)) = EM (Finsupp.single (x * g⁻¹) m) := fun g x m => by
    change Representation.ind (⊥ : Subgroup G).subtype ρ₀ g (P2mS26K3.E ρ₀ (Finsupp.single x m)) = _
    rw [P2mS26K3.ind_E, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

  let fwdPi : (I →ₗ[k] W) →ₗ[k] (G → V) :=
    LinearMap.pi fun x => LinearMap.llcomp k M W W (W.ρ x) ∘ₗ LinearMap.lcomp k W (EM.toLinearMap ∘ₗ Finsupp.lsingle x)
  have fwdPi_apply : ∀ (φ : I →ₗ[k] W) (x : G) (m : M), fwdPi φ x m = W.ρ x (φ (EM (Finsupp.single x m))) :=
    fun φ x m => rfl

  let twInv : (G → V) →ₗ[k] (G → V) := LinearMap.pi fun x => LinearMap.llcomp k M W W (W.ρ x⁻¹) ∘ₗ LinearMap.proj x
  let bwdPi : (G → V) →ₗ[k] (I →ₗ[k] W) :=
    LinearMap.lcomp k W EM.symm.toLinearMap ∘ₗ
      (Finsupp.lsum k : (G → M →ₗ[k] W) ≃ₗ[k] ((G →₀ M) →ₗ[k] W)).toLinearMap ∘ₗ twInv
  have bwdPi_apply : ∀ (F : G → V) (x : G) (m : M), bwdPi F (EM (Finsupp.single x m)) = W.ρ x⁻¹ (F x m) := fun F x m => by
    change (Finsupp.lsum k (fun x => W.ρ x⁻¹ ∘ₗ F x)) (EM.symm (EM (Finsupp.single x m))) = _
    rw [LinearEquiv.symm_apply_apply, Finsupp.lsum_single]
    rfl
  have h1 : fwdPi ∘ₗ bwdPi = LinearMap.id := by
    apply LinearMap.ext
    intro F
    funext x
    apply LinearMap.ext
    intro m
    rw [LinearMap.comp_apply, fwdPi_apply, bwdPi_apply, ρWinv, LinearMap.id_apply]
  have h2 : bwdPi ∘ₗ fwdPi = LinearMap.id := by
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro y
    obtain ⟨f, rfl⟩ := EM.surjective y
    rw [LinearMap.comp_apply, LinearMap.id_apply]
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f f' hf hf' => rw [map_add, map_add, map_add, hf, hf']
    | single x m => rw [bwdPi_apply, fwdPi_apply, ρWinv']
  let Θ₀ : (I →ₗ[k] W) ≃ₗ[k] (G → V) := LinearEquiv.ofLinear fwdPi bwdPi h1 h2
  let Θ : A ≃ₗ[k] J := Θ₀.trans ((Finsupp.linearEquivFunOnFinite k V G).symm.trans EV)
  have hΘ : ∀ φ : A, Θ φ = EV ((Finsupp.linearEquivFunOnFinite k V G).symm (fwdPi (ofA φ))) := fun φ => rfl

  have hequiv : ∀ g : G, Θ.toLinearMap ∘ₗ A.ρ g = J.ρ g ∘ₗ Θ.toLinearMap := by
    intro g
    apply LinearMap.ext
    intro φ
    change Θ (A.ρ g φ) = J.ρ g (Θ φ)
    rw [hΘ, hΘ]
    change _ = Representation.ind (⊥ : Subgroup G).subtype σ₀ g (P2mS26K3.E σ₀ _)
    rw [P2mS26K3.ind_E]
    change EV _ = EV _
    congr 1
    apply Finsupp.ext
    intro x
    rw [P2mS26K3.lmapDomain_apply]
    change fwdPi (ofA (A.ρ g φ)) x = fwdPi (ofA φ) (x * g)
    apply LinearMap.ext
    intro m
    rw [fwdPi_apply, fwdPi_apply, hAρ, LinearMap.comp_apply, LinearMap.comp_apply, hIρ, inv_inv, ← Module.End.mul_apply,
      ← map_mul]
  have hequiv' : ∀ (g : G) φ, Θ (A.ρ g φ) = J.ρ g (Θ φ) := fun g φ => LinearMap.congr_fun (hequiv g) φ
  have hequiv_symm : ∀ g : G, Θ.symm.toLinearMap ∘ₗ J.ρ g = A.ρ g ∘ₗ Θ.symm.toLinearMap := by
    intro g
    apply LinearMap.ext
    intro y
    obtain ⟨φ, rfl⟩ := Θ.surjective y
    change Θ.symm (J.ρ g (Θ φ)) = A.ρ g (Θ.symm (Θ φ))
    rw [← hequiv', Θ.symm_apply_apply, Θ.symm_apply_apply]
  let e : A ≅ J :=
    { hom := Rep.ofHom ⟨Θ.toLinearMap, hequiv⟩
      inv := Rep.ofHom ⟨Θ.symm.toLinearMap, hequiv_symm⟩
      hom_inv_id := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => Θ.symm_apply_apply x))
      inv_hom_id := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun y => Θ.apply_symm_apply y)) }
  obtain ⟨f⟩ := Rep.nonempty_tateCohomology_iso_of_iso e q
  exact Limits.IsZero.of_iso (Rep.isZero_tateCohomology_indBot TV q) f

end

end S_Rep_isZero_tateCohomology_ihom_indBot_trivial
end P2MW
export P2MW.S_Rep_isZero_tateCohomology_ihom_indBot_trivial (solution)
