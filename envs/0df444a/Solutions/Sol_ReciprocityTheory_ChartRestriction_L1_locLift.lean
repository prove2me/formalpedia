-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.locLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:57:14.388669+00:00
-- url     : https://prove2.me/submissions/10572f83-d1b5-4617-91da-ddea0c1bb804

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_exists_e_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_le_iff_of_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_fix_KQ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_mem_Aio
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_mem_nonunits_Aio


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane Pointwise
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {d l : ℕ} [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (e : Om d →+* PadicAlgCl l)
    (he : ∀ x : Om d, algebraMap (PadicAlgCl l) ℂ_[l] (e x) = ι (x : ℂ))
    (ρ : PadicAlgCl l ≃ₐ[IntermediateField.adjoin ℚ_[l] {e (algebraMap (KQ d) (Om d) (sqK d))}] PadicAlgCl l)
    (hρ : ∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖ρ z - z‖ < 1) :
    ∃ σ : Om d ≃ₐ[KQ d] Om d, InertiaEl (Aio d l ι) σ ∧ ∀ x : Om d, e (σ x) = ρ (e x) := by
  have hinj : Function.Injective e := e.injective
  choose g hg using exists_e_eq e (ρ : PadicAlgCl l →+* PadicAlgCl l)
  choose g' hg' using exists_e_eq e (ρ.symm : PadicAlgCl l →+* PadicAlgCl l)
  have hg1 : ∀ x, e (g x) = ρ (e x) := hg
  have hg2 : ∀ x, e (g' x) = ρ.symm (e x) := hg'
  let σ : Om d ≃ₐ[KQ d] Om d :=
    { toFun := g
      invFun := g'
      left_inv := fun x => hinj (by rw [hg2, hg1, AlgEquiv.symm_apply_apply])
      right_inv := fun x => hinj (by rw [hg1, hg2, AlgEquiv.apply_symm_apply])
      map_mul' := fun x y => hinj (by rw [hg1, map_mul, map_mul, map_mul, hg1, hg1])
      map_add' := fun x y => hinj (by rw [hg1, map_add, map_add, map_add, hg1, hg1])
      commutes' := fun k => hinj (by rw [hg1, fix_KQ]) }
  have hσ : ∀ x, e (σ x) = ρ (e x) := hg1
  have hn : ∀ x : Om d, ‖ι (x : ℂ)‖ = ‖e x‖ := fun x => by
    rw [← he, ← PadicComplex.coe_eq, PadicComplex.norm_extends]
  have hiff : ∀ x : Om d, σ x ∈ Aio d l ι ↔ x ∈ Aio d l ι := fun x => by
    rw [mem_Aio, mem_Aio, hn, hn, hσ]
    exact norm_le_iff_of_res (ρ : PadicAlgCl l →+* PadicAlgCl l) hρ (e x)
  refine ⟨σ, ⟨?_, ?_⟩, hσ⟩
  · show σ • Aio d l ι = Aio d l ι
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← hiff]
    have : σ (σ⁻¹ • x) = x := σ.apply_symm_apply x
    rw [this]
  · intro x hx
    rw [mem_nonunits_Aio]
    rw [hn, map_sub, hσ]
    exact hρ _ (by rw [← hn]; exact (mem_Aio ι x).1 hx)
end ReciprocityTheory.ChartRestriction.L1
