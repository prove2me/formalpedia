-- Prove2me | solution 1 for Rep.isZero_tateCohomology_indBot_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/72814e81-29a2-5590-8dcf-bfd88cd51720

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

namespace P2MW.S_Rep_isZero_tateCohomology_indBot_tensor

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace P2mS26IndTens
p2m_open "Representation TensorProduct Representation.TensorProduct"

variable {k G : Type*} [CommRing k] [Group G]

section model
variable {W : Type*} [AddCommGroup W] [Module k W] (ρ : Representation k (⊥ : Subgroup G) W)

lemma ker_tprod_bot_eq_bot :
    Representation.Coinvariants.ker (V := MonoidAlgebra k G ⊗[k] W)
      (Representation.tprod ((Representation.leftRegular k G).comp (⊥ : Subgroup G).subtype) ρ) = ⊥ := by
  rw [Representation.Coinvariants.ker, Submodule.span_eq_bot]
  rintro _ ⟨⟨g, v⟩, rfl⟩
  have hg : g = 1 := Subsingleton.elim _ _
  simp [hg]

def E [DecidableEq G] : (G →₀ W) ≃ₗ[k] Representation.IndV (⊥ : Subgroup G).subtype ρ :=
  (finsuppScalarLeft k W G).symm.trans <|
    ((MonoidAlgebra.coeffLinearEquiv k).rTensor W).symm.trans
      ((Submodule.quotEquivOfEqBot _ (ker_tprod_bot_eq_bot ρ)).symm :
        (MonoidAlgebra k G ⊗[k] W) ≃ₗ[k] Representation.Coinvariants (V := MonoidAlgebra k G ⊗[k] W)
          (Representation.tprod ((Representation.leftRegular k G).comp (⊥ : Subgroup G).subtype) ρ))

lemma E_single [DecidableEq G] (g : G) (w : W) :
    E ρ (Finsupp.single g w) = Representation.IndV.mk (⊥ : Subgroup G).subtype ρ g w := by
  rw [E, LinearEquiv.trans_apply, finsuppScalarLeft_symm_apply_single, LinearEquiv.trans_apply]
  rfl

end model

section untwist
variable (A B : Rep k G)

lemma rho_self_inv (x : G) (v : B) : B.ρ x (B.ρ x⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

lemma rho_inv_self (x : G) (v : B) : B.ρ x⁻¹ (B.ρ x v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

def fwd : ((G →₀ A) ⊗[k] B) →ₗ[k] (G →₀ (A ⊗[k] B)) :=
  TensorProduct.lift (Finsupp.lsum k fun x =>
    ((TensorProduct.mk k A B).compl₂ (B.ρ x)).compr₂ (Finsupp.lsingle x))

lemma fwd_tmul (x : G) (a : A) (b : B) :
    fwd A B (Finsupp.single x a ⊗ₜ[k] b) = Finsupp.single x (a ⊗ₜ[k] B.ρ x b) := by
  simp only [fwd, TensorProduct.lift.tmul, Finsupp.lsum_single, LinearMap.compr₂_apply, LinearMap.compl₂_apply,
    TensorProduct.mk_apply, Finsupp.lsingle_apply]

def bwd : (G →₀ (A ⊗[k] B)) →ₗ[k] ((G →₀ A) ⊗[k] B) :=
  Finsupp.lsum k fun x =>
    TensorProduct.lift (((TensorProduct.mk k (G →₀ A) B).comp (Finsupp.lsingle x)).compl₂ (B.ρ x⁻¹))

lemma bwd_single (x : G) (a : A) (b : B) :
    bwd A B (Finsupp.single x (a ⊗ₜ[k] b)) = Finsupp.single x a ⊗ₜ[k] B.ρ x⁻¹ b := by
  simp only [bwd, Finsupp.lsum_single, TensorProduct.lift.tmul, LinearMap.compl₂_apply, LinearMap.comp_apply,
    TensorProduct.mk_apply, Finsupp.lsingle_apply]

lemma fwd_bwd : fwd A B ∘ₗ bwd A B = LinearMap.id := by
  classical
  apply Finsupp.lhom_ext
  intro x t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t t' ht ht' => rw [Finsupp.single_add, map_add, map_add, ht, ht']
  | tmul a b => rw [LinearMap.comp_apply, bwd_single, fwd_tmul, rho_self_inv, LinearMap.id_apply]

lemma bwd_fwd : bwd A B ∘ₗ fwd A B = LinearMap.id := by
  apply TensorProduct.ext'
  intro f b
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [TensorProduct.add_tmul, map_add, map_add, hf, hg]
  | single x a => rw [LinearMap.comp_apply, fwd_tmul, bwd_single, rho_inv_self, LinearMap.id_apply]

def V : ((G →₀ A) ⊗[k] B) ≃ₗ[k] (G →₀ (A ⊗[k] B)) :=
  LinearEquiv.ofLinear (fwd A B) (bwd A B) (fwd_bwd A B) (bwd_fwd A B)

lemma V_tmul (x : G) (a : A) (b : B) :
    V A B (Finsupp.single x a ⊗ₜ[k] b) = Finsupp.single x (a ⊗ₜ[k] B.ρ x b) :=
  fwd_tmul A B x a b

end untwist
end P2mS26IndTens

end

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A B : Rep.{u} k G) (q : ℤ) :
    CategoryTheory.Limits.IsZero ((A.indBot ⊗ B).tateCohomology q) := by
  classical
  let ρA : Representation k (⊥ : Subgroup G) A := (Rep.res (⊥ : Subgroup G).subtype A).ρ
  let ρAB : Representation k (⊥ : Subgroup G) (A ⊗ B : Rep k G) := (Rep.res (⊥ : Subgroup G).subtype (A ⊗ B)).ρ
  let EA : (G →₀ A) ≃ₗ[k] (A.indBot : Type u) := P2mS26IndTens.E (G := G) ρA
  let EAB : (G →₀ (A ⊗ B : Rep k G)) ≃ₗ[k] ((A ⊗ B).indBot : Type u) := P2mS26IndTens.E (G := G) ρAB
  have hEA : ∀ (x : G) (a : A), EA (Finsupp.single x a) = A.indBotMk x a := fun x a => by
    change P2mS26IndTens.E ρA (Finsupp.single x a) = _
    rw [P2mS26IndTens.E_single]
    rfl
  have hEAB : ∀ (x : G) (t : (A ⊗ B : Rep k G)), EAB (Finsupp.single x t) = (A ⊗ B).indBotMk x t := fun x t => by
    change P2mS26IndTens.E ρAB (Finsupp.single x t) = _
    rw [P2mS26IndTens.E_single]
    rfl
  let Φ : ((A.indBot ⊗ B : Rep k G) : Type u) ≃ₗ[k] ((A ⊗ B).indBot : Type u) :=
    (TensorProduct.congr EA.symm (LinearEquiv.refl k B)).trans ((P2mS26IndTens.V A B).trans EAB)
  have hΦ : ∀ (x : G) (a : A) (b : B),
      Φ (A.indBotMk x a ⊗ₜ[k] b) = (A ⊗ B).indBotMk x (a ⊗ₜ[k] B.ρ x b) := fun x a b => by
    change EAB (P2mS26IndTens.V A B (TensorProduct.congr EA.symm (LinearEquiv.refl k B) (A.indBotMk x a ⊗ₜ[k] b))) = _
    rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, show EA.symm (A.indBotMk x a) = Finsupp.single x a from
      (LinearEquiv.symm_apply_eq EA).2 (hEA x a).symm, P2mS26IndTens.V_tmul, hEAB]

  have hgen : ∀ (g x : G) (a : A) (b : B),
      Φ ((A.indBot ⊗ B).ρ g (A.indBotMk x a ⊗ₜ[k] b)) = (A ⊗ B).indBot.ρ g (Φ (A.indBotMk x a ⊗ₜ[k] b)) := by
    intro g x a b
    rw [Rep.tensor_ρ, Representation.tprod_apply, TensorProduct.map_tmul, Rep.indBot_rho_indBotMk, hΦ, hΦ,
      Rep.indBot_rho_indBotMk, map_mul, Module.End.mul_apply, P2mS26IndTens.rho_inv_self]
  have hequiv : ∀ g : G, Φ.toLinearMap ∘ₗ (A.indBot ⊗ B).ρ g = (A ⊗ B).indBot.ρ g ∘ₗ Φ.toLinearMap := by
    intro g
    apply TensorProduct.ext'
    intro z b
    obtain ⟨f, rfl⟩ := EA.surjective z
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f f' hf hf' => rw [map_add, TensorProduct.add_tmul, map_add, map_add, hf, hf']
    | single x a =>
      change Φ ((A.indBot ⊗ B).ρ g (EA (Finsupp.single x a) ⊗ₜ[k] b)) = (A ⊗ B).indBot.ρ g (Φ (EA (Finsupp.single x a) ⊗ₜ[k] b))
      rw [hEA]
      exact hgen g x a b
  have hequiv' : ∀ (g : G) x, Φ ((A.indBot ⊗ B).ρ g x) = (A ⊗ B).indBot.ρ g (Φ x) := fun g x =>
    LinearMap.congr_fun (hequiv g) x
  have hequiv_symm : ∀ g : G, Φ.symm.toLinearMap ∘ₗ (A ⊗ B).indBot.ρ g = (A.indBot ⊗ B).ρ g ∘ₗ Φ.symm.toLinearMap := by
    intro g
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := Φ.surjective y
    change Φ.symm ((A ⊗ B).indBot.ρ g (Φ x)) = (A.indBot ⊗ B).ρ g (Φ.symm (Φ x))
    rw [← hequiv', Φ.symm_apply_apply, Φ.symm_apply_apply]
  let e : (A.indBot ⊗ B) ≅ (A ⊗ B).indBot :=
    { hom := Rep.ofHom ⟨Φ.toLinearMap, hequiv⟩
      inv := Rep.ofHom ⟨Φ.symm.toLinearMap, hequiv_symm⟩
      hom_inv_id := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => Φ.symm_apply_apply x))
      inv_hom_id := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun y => Φ.apply_symm_apply y)) }
  obtain ⟨f⟩ := Rep.nonempty_tateCohomology_iso_of_iso e q
  exact (Rep.isZero_tateCohomology_indBot (A ⊗ B) q).of_iso f

end S_Rep_isZero_tateCohomology_indBot_tensor
end P2MW
export P2MW.S_Rep_isZero_tateCohomology_indBot_tensor (solution)
