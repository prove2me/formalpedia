-- Prove2me | solution 1 for Rep.isZero_tateCohomology_ihom_indBot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/23ba958b-6c98-5b5c-b3b1-39e7d3639cbe

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

namespace P2MW.S_Rep_isZero_tateCohomology_ihom_indBot

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

namespace P2mS26FDacyc
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
    ((MonoidAlgebra.coeffLinearEquiv k).rTensor W).symm.trans
      ((Submodule.quotEquivOfEqBot _ (ker_tprod_bot_eq_bot ρ)).symm :
        (MonoidAlgebra k G ⊗[k] W) ≃ₗ[k] Representation.Coinvariants (V := MonoidAlgebra k G ⊗[k] W)
          (Representation.tprod ((Representation.leftRegular k G).comp (⊥ : Subgroup G).subtype) ρ))

lemma E_single [DecidableEq G] (g : G) (w : W) :
    E ρ (Finsupp.single g w) = Representation.IndV.mk (⊥ : Subgroup G).subtype ρ g w := by
  rw [E, LinearEquiv.trans_apply, finsuppScalarLeft_symm_apply_single, LinearEquiv.trans_apply]
  rfl

end model

variable [DecidableEq G]

abbrev EA (A : Rep.{u} k G) : (G →₀ A) ≃ₗ[k] (A.indBot : Type u) := E (G := G) (Rep.res (⊥ : Subgroup G).subtype A).ρ

lemma EA_single (A : Rep.{u} k G) (g : G) (a : A) : EA A (Finsupp.single g a) = A.indBotMk g a := by
  rw [EA, E_single]; rfl

lemma indBot_induction (A : Rep.{u} k G) {P : A.indBot → Prop} (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hmk : ∀ (g : G) (a : A), P (A.indBotMk g a)) (x : A.indBot) : P x := by
  obtain ⟨f, rfl⟩ := (EA A).surjective x
  induction f using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact h0
  | add f f' hf hf' => rw [map_add]; exact hadd _ _ hf hf'
  | single g a => rw [EA_single]; exact hmk g a

def proj (A : Rep.{u} k G) (g : G) : (A.indBot : Type u) →ₗ[k] A := Finsupp.lapply g ∘ₗ (EA A).symm.toLinearMap

lemma proj_indBotMk (A : Rep.{u} k G) (g g' : G) (a : A) :
    proj A g (A.indBotMk g' a) = if g' = g then a else 0 := by
  rw [proj, LinearMap.comp_apply, LinearEquiv.coe_coe,
    show (EA A).symm (A.indBotMk g' a) = Finsupp.single g' a from (LinearEquiv.symm_apply_eq _).2 (EA_single A g' a).symm,
    Finsupp.lapply_apply, Finsupp.single_apply]

variable [Fintype G] (A W : Rep.{u} k G)

def tw (g : G) : ((A.indBot : Type u) →ₗ[k] W) →ₗ[k] ((A : Type u) →ₗ[k] W) :=
  (LinearMap.compRight k (W.ρ g)) ∘ₗ (LinearMap.lcomp k W (A.indBotMk g))

omit [DecidableEq G] [Fintype G] in
lemma tw_apply (g : G) (f : (A.indBot : Type u) →ₗ[k] W) : tw A W g f = W.ρ g ∘ₗ f ∘ₗ A.indBotMk g := rfl

def Φ : ((A.indBot : Type u) →ₗ[k] W) →ₗ[k] (((ihom A).obj W).indBot : Type u) :=
  ∑ g : G, ((ihom A).obj W).indBotMk g ∘ₗ tw A W g

omit [DecidableEq G] in
lemma Φ_apply (f : (A.indBot : Type u) →ₗ[k] W) :
    Φ A W f = ∑ g : G, ((ihom A).obj W).indBotMk g (W.ρ g ∘ₗ f ∘ₗ A.indBotMk g) := by
  rw [Φ, LinearMap.sum_apply]
  rfl

omit [DecidableEq G] [Fintype G] in
lemma ihom_ρ_apply' (h : G) (f : (A.indBot : Type u) →ₗ[k] W) :
    ((ihom A.indBot).obj W).ρ h f = W.ρ h ∘ₗ f ∘ₗ A.indBot.ρ h⁻¹ :=
  Rep.ihom_obj_ρ_apply (A := A.indBot) (B := W) h f

omit [DecidableEq G] [Fintype G] in
lemma rho_inv_comp_indBotMk (h g : G) : A.indBot.ρ h⁻¹ ∘ₗ A.indBotMk g = A.indBotMk (g * h) := by
  refine LinearMap.ext fun a => ?_
  rw [LinearMap.comp_apply, Rep.indBot_rho_indBotMk, inv_inv]

omit [DecidableEq G] in

lemma Φ_equivariant (h : G) (f : (A.indBot : Type u) →ₗ[k] W) :
    Φ A W (((ihom A.indBot).obj W).ρ h f) = ((ihom A).obj W).indBot.ρ h (Φ A W f) := by
  rw [Φ_apply, Φ_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => ?_
  rw [Equiv.coe_mulRight, Rep.indBot_rho_indBotMk, mul_inv_cancel_right, ihom_ρ_apply',
    LinearMap.comp_assoc, LinearMap.comp_assoc, rho_inv_comp_indBotMk, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc,
    ← Module.End.mul_eq_comp, ← map_mul, LinearMap.comp_assoc]

lemma Φ_injective : Function.Injective (Φ A W) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => ?_
  rw [Φ_apply] at hf

  have hc : ∀ g : G, W.ρ g ∘ₗ f ∘ₗ A.indBotMk g = 0 := by
    intro g₀
    have := congrArg (proj ((ihom A).obj W) g₀) hf
    rw [map_sum, map_zero, Finset.sum_eq_single g₀ (fun g _ hg => by rw [proj_indBotMk, if_neg hg]) (fun h => (h (Finset.mem_univ _)).elim),
      proj_indBotMk, if_pos rfl] at this
    exact this
  refine Representation.IndV.hom_ext _ _ fun g => ?_
  rw [LinearMap.zero_comp]
  change f ∘ₗ A.indBotMk g = 0
  have h1 := congrArg (fun φ => W.ρ g⁻¹ ∘ₗ φ) (hc g)
  simp only [LinearMap.comp_zero] at h1
  rwa [← LinearMap.comp_assoc, ← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one, Module.End.one_eq_id,
    LinearMap.id_comp] at h1

lemma Φ_surjective : Function.Surjective (Φ A W) := by
  intro y
  induction y using indBot_induction ((ihom A).obj W) with
  | h0 => exact ⟨0, map_zero _⟩
  | hadd x y hx hy =>
    obtain ⟨f, rfl⟩ := hx
    obtain ⟨f', rfl⟩ := hy
    exact ⟨f + f', map_add _ _ _⟩
  | hmk g₀ φ₀ =>
    obtain ⟨φ, rfl⟩ : ∃ φ : (A : Type u) →ₗ[k] W, φ = φ₀ := ⟨φ₀, rfl⟩
    refine ⟨(W.ρ g₀⁻¹ ∘ₗ φ) ∘ₗ proj A g₀, ?_⟩
    rw [Φ_apply, Finset.sum_eq_single g₀ ?_ (fun h => (h (Finset.mem_univ _)).elim)]
    · congr 1
      refine LinearMap.ext fun a => ?_
      change W.ρ g₀ (W.ρ g₀⁻¹ (φ (proj A g₀ (A.indBotMk g₀ a)))) = φ a
      rw [proj_indBotMk, if_pos rfl, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    · intro g _ hg
      have h0 : (W.ρ g ∘ₗ ((W.ρ g₀⁻¹ ∘ₗ φ) ∘ₗ proj A g₀) ∘ₗ A.indBotMk g) = 0 :=
        LinearMap.ext fun a => by
          change W.ρ g (W.ρ g₀⁻¹ (φ (proj A g₀ (A.indBotMk g a)))) = 0
          rw [proj_indBotMk, if_neg hg, map_zero, map_zero, map_zero]
      rw [h0]
      exact map_zero _

end

end P2mS26FDacyc

open P2mS26FDacyc in
theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A W : Rep.{u} k G) (q : ℤ) :
    CategoryTheory.Limits.IsZero (((ihom A.indBot).obj W).tateCohomology q) := by
  classical
  let H : Rep.{u} k G := (ihom A).obj W
  let Ψ := LinearEquiv.ofBijective (Φ A W) ⟨Φ_injective A W, Φ_surjective A W⟩
  have hequiv' : ∀ (g : G) f, Ψ (((ihom A.indBot).obj W).ρ g f) = H.indBot.ρ g (Ψ f) := fun g f => Φ_equivariant A W g f
  have hequiv : ∀ g : G, Ψ.toLinearMap ∘ₗ ((ihom A.indBot).obj W).ρ g = H.indBot.ρ g ∘ₗ Ψ.toLinearMap :=
    fun g => LinearMap.ext fun f => hequiv' g f
  have hequiv_symm : ∀ g : G, Ψ.symm.toLinearMap ∘ₗ H.indBot.ρ g = ((ihom A.indBot).obj W).ρ g ∘ₗ Ψ.symm.toLinearMap := by
    intro g
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := Ψ.surjective y
    change Ψ.symm (H.indBot.ρ g (Ψ x)) = ((ihom A.indBot).obj W).ρ g (Ψ.symm (Ψ x))
    rw [← hequiv', Ψ.symm_apply_apply, Ψ.symm_apply_apply]
  let e : ((ihom A.indBot).obj W) ≅ H.indBot :=
    { hom := Rep.ofHom ⟨Ψ.toLinearMap, hequiv⟩
      inv := Rep.ofHom ⟨Ψ.symm.toLinearMap, hequiv_symm⟩
      hom_inv_id := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => Ψ.symm_apply_apply x))
      inv_hom_id := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun y => Ψ.apply_symm_apply y)) }
  obtain ⟨f⟩ := Rep.nonempty_tateCohomology_iso_of_iso e q
  exact (Rep.isZero_tateCohomology_indBot H q).of_iso f

end S_Rep_isZero_tateCohomology_ihom_indBot
end P2MW
export P2MW.S_Rep_isZero_tateCohomology_ihom_indBot (solution)
