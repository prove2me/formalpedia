-- Prove2me | solution 1 for Rep.subsingleton_tateH0_ind_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/3ef36c9d-433f-5f05-9ffc-317328725fe1

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_subsingleton_tateH0_ind_bot

set_option autoImplicit false
universe u
open CategoryTheory Rep
set_option maxHeartbeats 1600000

namespace P2mS26A6
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
    (TensorProduct.congr (MonoidAlgebra.coeffLinearEquiv k).symm (LinearEquiv.refl k A)).trans
      ((Submodule.quotEquivOfEqBot _ (ker_tprod_bot_eq_bot ρ)).symm :
        (MonoidAlgebra k G ⊗[k] A) ≃ₗ[k] Representation.Coinvariants (V := MonoidAlgebra k G ⊗[k] A)
          (Representation.tprod ((Representation.leftRegular k G).comp (⊥ : Subgroup G).subtype) ρ))

lemma E_single [DecidableEq G] (g : G) (a : A) : E ρ (Finsupp.single g a) = Representation.IndV.mk (⊥ : Subgroup G).subtype ρ g a := by
  rw [E, LinearEquiv.trans_apply, finsuppScalarLeft_symm_apply_single, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul]
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

private lemma _root_.P2mS26A6.lmapDomain_apply (h : G) (f : G →₀ A) (y : G) :
    Finsupp.lmapDomain A k (fun x => x * h⁻¹) f y = f (y * h) := by
  rw [Finsupp.lmapDomain_apply]
  conv_lhs => rw [← mul_inv_cancel_right y h]
  exact Finsupp.mapDomain_apply (mul_left_injective h⁻¹) f (y * h)

p2m_export "P2mS26A6" "lmapDomain_apply"
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
end P2mS26A6

open CategoryTheory Rep

theorem solution {k G : Type*} [CommRing k] [Group G] [Fintype G]
    (A : Rep k (⊥ : Subgroup G)) : Subsingleton (Rep.ind (⊥ : Subgroup G).subtype A).tateH0 := by
  classical

  refine ⟨fun x y => ?_⟩
  suffices h : ∀ z : (Rep.ind (⊥ : Subgroup G).subtype A).tateH0, z = 0 by rw [h x, h y]
  intro z
  induction z using Submodule.Quotient.induction_on with | _ v =>
  rw [Submodule.Quotient.mk_eq_zero]
  obtain ⟨f, hf⟩ := (P2mS26A6.E A.ρ).surjective (v : Representation.IndV (⊥ : Subgroup G).subtype A.ρ)
  have hinv : ∀ h, Representation.ind (⊥ : Subgroup G).subtype A.ρ h (P2mS26A6.E A.ρ f) = P2mS26A6.E A.ρ f := by
    intro h; rw [hf]; exact (Representation.mem_invariants _ _).1 v.2 h
  have hconst : f = ∑ y, Finsupp.single y (f 1) := by
    conv_lhs => rw [← Finsupp.univ_sum_single f]
    exact Finset.sum_congr rfl fun y _ => by rw [P2mS26A6.apply_eq_apply_one_of_invariant A.ρ f hinv y]
  have hc : P2mS26A6.E A.ρ f = P2mS26A6.E A.ρ (∑ y, Finsupp.single y (f 1)) := by rw [← hconst]
  refine ⟨Representation.Coinvariants.mk _ (P2mS26A6.E A.ρ (Finsupp.single 1 (f 1))), Subtype.ext ?_⟩
  rw [Representation.normBar_mk, Representation.coe_normToInvariants_apply, ← hf, hc]
  exact P2mS26A6.norm_E_single_one A.ρ (f 1)

end S_Rep_subsingleton_tateH0_ind_bot
end P2MW
export P2MW.S_Rep_subsingleton_tateH0_ind_bot (solution)
