-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.normHom_eq_algebra_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:33:50.834332+00:00
-- url     : https://prove2.me/submissions/0749ede7-9391-40da-b60b-8d8f0d9a5a46

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormOpenA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_normHom_apply
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_coe_sum_KbarMult
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_degLK_eq_finrank
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_degLK_pos
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finite_GalLK


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (y : KbarMult p)
    (hy : y ∈ multOf p L) :
    ((Additive.toMul (normHom p K L y) : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
      ((Algebra.norm K (⟨((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p), hy⟩ :
        IntermediateField.extendScalars h) : K) : PadicAlgCl p) := by
  have := finite_GalLK (p := p) (K := K) hL
  have := Fintype.ofFinite (GK p K ⧸ subG p K L)
  have hfin : FiniteDimensional K (IntermediateField.extendScalars h) := by
    apply Module.finite_of_finrank_pos
    rw [← degLK_eq_finrank h]
    exact degLK_pos hL
  have hbij : Bijective (fun c : GK p K ⧸ subG p K L =>
      ((c.out : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) : PadicAlgCl p →ₐ[K] PadicAlgCl p).comp
        (IntermediateField.extendScalars h).val) := by
    apply Function.Injective.bijective_of_nat_card_le
    · intro c c' hcc
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
      apply QuotientGroup.eq.2
      intro x hx
      have h1 : c.out x = c'.out x := DFunLike.congr_fun hcc (⟨x, hx⟩ : IntermediateField.extendScalars h)
      show c.out⁻¹ (c'.out x) = x
      rw [← h1]
      exact c.out.symm_apply_apply x
    · rw [Nat.card_eq_fintype_card, AlgHom.card, ← degLK_eq_finrank h]
      exact le_of_eq rfl
  have h1 := Algebra.norm_eq_prod_embeddings K (PadicAlgCl p)
    (⟨((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p), hy⟩ : IntermediateField.extendScalars h)
  refine Eq.trans ?_ h1.symm
  rw [normHom_apply]
  refine (coe_sum_KbarMult _ _).trans ?_
  exact Fintype.prod_bijective _ hbij _ _ fun c => rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField
