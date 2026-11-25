-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.exists_coset_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:15:29.797359+00:00
-- url     : https://prove2.me/submissions/b9da9255-6504-483c-9434-1cb4cebec023

import Definitions.Def_ReciprocityTheory_DualLattices_MemMapAugmentationIdealComapPullbackQuotient
import Definitions.Def_ReciprocityTheory_DualLattices_MemSupOfRestrictToSubgroupMemSq
import Theorems.Thm_ReciprocityTheory_PGsh_L2_exists_basis_map_restrictToSubgroup
import Theorems.Thm_ReciprocityTheory_PGsh_L2_apply_add_of_mem_map_pullbackQuotient
import Theorems.Thm_ReciprocityTheory_PGsh_L2_eq_zero_of_sum_mul_coset_eq_zero
import Theorems.Thm_ReciprocityTheory_PGsh_L2_exists_coset_invariant_coefficients
import Theorems.Thm_ReciprocityTheory_PGsh_L2_exists_family_valuation_det_eq_one
import Theorems.Thm_ReciprocityTheory_PGsh_L2_mem_map_comap_pullbackQuotient


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∃ f : K → N → C, (∀ j, f j ∈ AA.carrier) ∧ ∀ g ∈ AA.carrier,
      ∃! b : K → N → C, (∀ j, b j ∈ (AA.carrier.comap (pullQ (R := R) K)).map (pullQ K)) ∧
        g = ∑ j, b j * f j := by
  obtain ⟨β, hβ, hAK⟩ := exists_basis_map_restrictToSubgroup hv AA K
  obtain ⟨f, hf, hgood⟩ := exists_family_valuation_det_eq_one hv AA K β hβ hAK
  refine ⟨f, hf, fun g hg => ?_⟩
  obtain ⟨b, hbA, hbinv, hgb⟩ := exists_coset_invariant_coefficients hv AA K β hβ hAK f hf hgood hg
  refine ⟨b, ⟨fun j => mem_map_comap_pullbackQuotient AA K (hbA j) (hbinv j), hgb⟩, ?_⟩
  rintro b' ⟨hb', hgb'⟩
  funext j x
  have hc := eq_zero_of_sum_mul_coset_eq_zero (v := v) K β hβ f hgood x (fun j => b' j x - b j x) (fun k => by
    have e1 := congrFun hgb (x + k)
    have e2 := congrFun hgb' (x + k)
    simp only [Finset.sum_apply, Pi.mul_apply] at e1 e2
    have h1 : ∀ j, b' j x - b j x = b' j (x + k) - b j (x + k) := fun j => by
      rw [apply_add_of_mem_map_pullbackQuotient K _ (hb' j) x k, hbinv j x k]
    simp only [h1, sub_mul, Finset.sum_sub_distrib]
    rw [← e1, ← e2, sub_self])
  exact sub_eq_zero.mp (congrFun hc j)
end ReciprocityTheory.PGsh.L2
