-- Prove2me | solution 1 for Rep.exists_hom_dimShiftDownObj_trivial_leftRegular
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/5fae777f-8dcd-576e-9aed-3c6e24279676

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Theorems.Thm_Rep_indBotPi_indBotMk
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_exists_hom_dimShiftDownObj_trivial_leftRegular

set_option autoImplicit false
universe u
open CategoryTheory Rep
set_option maxHeartbeats 1600000

namespace P2mS26HB0
p2m_open "Representation TensorProduct Representation.TensorProduct"

variable {k G : Type*} [CommRing k] [Group G]

section model
variable {A : Type*} [AddCommGroup A] [Module k A] (ρ : Representation k (⊥ : Subgroup G) A)

lemma ker_tprod_bot_eq_bot :
    Representation.Coinvariants.ker (V := MonoidAlgebra k G ⊗[k] A) (Representation.tprod ((Representation.leftRegular k G).comp (⊥ : Subgroup G).subtype) ρ) = ⊥ := by
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

lemma E_single [DecidableEq G] (g : G) (a : A) : E ρ (Finsupp.single g a) = Representation.IndV.mk (⊥ : Subgroup G).subtype ρ g a := by
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

private lemma _root_.P2mS26HB0.lmapDomain_apply (h : G) (f : G →₀ A) (y : G) :
    Finsupp.lmapDomain A k (fun x => x * h⁻¹) f y = f (y * h) := by
  rw [Finsupp.lmapDomain_apply]
  conv_lhs => rw [← mul_inv_cancel_right y h]
  exact Finsupp.mapDomain_apply (mul_left_injective h⁻¹) f (y * h)

p2m_export "P2mS26HB0" "lmapDomain_apply"
variable [Fintype G]

lemma norm_E [DecidableEq G] (f : G →₀ A) :
    (Representation.ind (⊥ : Subgroup G).subtype ρ).norm (E ρ f) = E ρ (∑ h, Finsupp.lmapDomain A k (fun x => x * h⁻¹) f) := by
  simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply, map_sum, ind_E]

lemma sum_lmapDomain_apply (f : G →₀ A) (y : G) :
    (∑ h, Finsupp.lmapDomain A k (fun x => x * h⁻¹) f) y = ∑ x, f x := by
  rw [Finsupp.finsetSum_apply]
  simp only [lmapDomain_apply]
  exact Fintype.sum_equiv (Equiv.mulLeft y) _ _ (fun _ => rfl)

omit [Fintype G] in

lemma apply_eq_apply_one_of_invariant [DecidableEq G] (f : G →₀ A)
    (hf : ∀ h, Representation.ind (⊥ : Subgroup G).subtype ρ h (E ρ f) = E ρ f) (y : G) : f y = f 1 := by
  have := hf y
  rw [ind_E, (E ρ).injective.eq_iff] at this
  have := DFunLike.congr_fun this 1
  rw [lmapDomain_apply, one_mul] at this
  exact this

lemma norm_E_single_one [DecidableEq G] (c : A) :
    (Representation.ind (⊥ : Subgroup G).subtype ρ).norm (E ρ (Finsupp.single 1 c)) = E ρ (∑ y, Finsupp.single y c) := by
  rw [norm_E]
  congr 1
  simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, one_mul]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun _ => rfl)

end model
end P2mS26HB0

theorem solution {k G : Type u} [CommRing k] [Group G] :
    ∃ j : (Rep.trivial k G k).dimShiftDownObj ⟶ Rep.leftRegularFinsupp k G,
      Function.Injective j.hom ∧
      (∀ x, Finsupp.linearCombination k (fun _ : G => (1 : k)) (j.hom x) = 0) ∧
      (∀ f : G →₀ k, Finsupp.linearCombination k (fun _ : G => (1 : k)) f = 0 → f ∈ LinearMap.range j.hom.toLinearMap) ∧
      (∀ g : G, ∃ d : (Rep.trivial k G k).dimShiftDownObj, j.hom d = Finsupp.single g 1 - Finsupp.single 1 1) := by
  classical

  let T : Rep.{u} k G := Rep.trivial k G k
  let ρ₀ : Representation k (⊥ : Subgroup G) k := (Rep.res (⊥ : Subgroup G).subtype T).ρ
  let E := P2mS26HB0.E (G := G) ρ₀

  let ψ : T.indBot →ₗ[k] (G →₀ k) := (Finsupp.lmapDomain k k (fun g : G => g⁻¹)) ∘ₗ E.symm.toLinearMap
  have hψE : ∀ f : G →₀ k, ψ (E f) = Finsupp.lmapDomain k k (fun g : G => g⁻¹) f := fun f => by
    show Finsupp.lmapDomain k k (fun g : G => g⁻¹) (E.symm (E f)) = _
    rw [LinearEquiv.symm_apply_apply]

  have hreg : ∀ (g : G) (f : G →₀ k), (Rep.leftRegularFinsupp k G).ρ g f = Finsupp.lmapDomain k k (g * ·) f := fun g f => rfl
  have hequiv : ∀ g : G, ψ ∘ₗ T.indBot.ρ g = (Rep.leftRegularFinsupp k G).ρ g ∘ₗ ψ := by
    intro g
    apply LinearMap.ext; intro x
    obtain ⟨f, rfl⟩ := E.surjective x
    show ψ (Representation.ind (⊥ : Subgroup G).subtype ρ₀ g (E f)) = (Rep.leftRegularFinsupp k G).ρ g (ψ (E f))
    rw [P2mS26HB0.ind_E, hψE, hψE, hreg, ← LinearMap.comp_apply, ← Finsupp.lmapDomain_comp,
      ← LinearMap.comp_apply, ← Finsupp.lmapDomain_comp]
    congr 2
    funext x
    simp [mul_inv_rev]
  let Φ : T.indBot ⟶ Rep.leftRegularFinsupp k G := Rep.ofHom ⟨ψ, hequiv⟩

  have hπE : ∀ f : G →₀ k, (Rep.indBotπ T).hom (E f) = Finsupp.linearCombination k (fun _ : G => (1 : k)) f := by
    intro f
    have : (Rep.indBotπ T).hom.toLinearMap ∘ₗ E.toLinearMap = Finsupp.linearCombination k (fun _ : G => (1 : k)) := by
      apply Finsupp.lhom_ext
      intro g r
      show (Rep.indBotπ T).hom (E (Finsupp.single g r)) = Finsupp.linearCombination k (fun _ : G => (1 : k)) (Finsupp.single g r)
      rw [P2mS26HB0.E_single, Finsupp.linearCombination_single]
      exact (Rep.indBotPi_indBotMk T g r).trans (by simp [T])
    exact LinearMap.congr_fun this f
  have hεinv : ∀ f : G →₀ k, Finsupp.linearCombination k (fun _ : G => (1 : k)) (Finsupp.lmapDomain k k (fun g : G => g⁻¹) f)
      = Finsupp.linearCombination k (fun _ : G => (1 : k)) f := by
    intro f
    rw [Finsupp.lmapDomain_apply, Finsupp.linearCombination_mapDomain]
    rfl
  refine ⟨(T.dimShiftDown).f ≫ Φ, ?_, ?_, ?_, ?_⟩
  ·
    intro x y hxy
    apply Subtype.ext
    apply E.symm.injective
    apply Finsupp.mapDomain_injective (inv_injective (G := G))
    exact hxy
  ·
    intro x
    obtain ⟨f, hf⟩ := E.surjective (x : T.indBot)
    show Finsupp.linearCombination k (fun _ : G => (1 : k)) (ψ (x : T.indBot)) = 0
    rw [← hf, hψE, hεinv, ← hπE, hf]
    exact x.2
  ·
    intro f hf
    refine ⟨⟨E (Finsupp.lmapDomain k k (fun g : G => g⁻¹) f), ?_⟩, ?_⟩
    · show (Rep.indBotπ T).hom (E _) = 0
      rw [hπE, hεinv, hf]
    · show ψ (E _) = f
      rw [hψE, ← LinearMap.comp_apply, ← Finsupp.lmapDomain_comp]
      convert LinearMap.id_apply (R := k) f using 2
      rw [show ((fun g : G => g⁻¹) ∘ fun g : G => g⁻¹) = id from funext fun g => inv_inv g]
      exact Finsupp.lmapDomain_id k k
  ·
    intro g
    refine ⟨⟨E (Finsupp.single g⁻¹ 1 - Finsupp.single 1 1), ?_⟩, ?_⟩
    · show (Rep.indBotπ T).hom (E _) = 0
      rw [hπE, map_sub, Finsupp.linearCombination_single, Finsupp.linearCombination_single, sub_self]
    · show ψ (E _) = _
      rw [hψE, map_sub, Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
        Finsupp.mapDomain_single, inv_inv, inv_one]

end S_Rep_exists_hom_dimShiftDownObj_trivial_leftRegular
end P2MW
export P2MW.S_Rep_exists_hom_dimShiftDownObj_trivial_leftRegular (solution)
