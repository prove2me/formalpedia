-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.mem_of_restrictToSubgroup_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:11:43.353315+00:00
-- url     : https://prove2.me/submissions/b0fe74c9-fef6-4c64-b3dd-b49672d991f5

import Definitions.Def_ReciprocityTheory_DualLattices_MemMapAugmentationIdealComapPullbackQuotient
import Definitions.Def_ReciprocityTheory_DualLattices_MemSupOfRestrictToSubgroupMemSq
import Theorems.Thm_ReciprocityTheory_PGsh_L2_exists_basis_map_restrictToSubgroup
import Theorems.Thm_ReciprocityTheory_PGsh_L2_eq_zero_of_sum_mul_coset_eq_zero
import Theorems.Thm_ReciprocityTheory_PGsh_L2_exists_coset_invariant_coefficients
import Theorems.Thm_ReciprocityTheory_PGsh_L2_exists_family_valuation_det_eq_one
import Theorems.Thm_ReciprocityTheory_PGsh_L2_mem_map_augmentationIdeal_comap_pullbackQuotient


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
    ∀ g ∈ AA.carrier, resK (R := R) K g = 0 →
      g ∈ (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) *
        AA.carrier := by
  intro g hg hres
  obtain ⟨β, hβ, hAK⟩ := exists_basis_map_restrictToSubgroup hv AA K
  obtain ⟨f, hf, hgood⟩ := exists_family_valuation_det_eq_one hv AA K β hβ hAK
  obtain ⟨b, hbA, hbinv, hgb⟩ := exists_coset_invariant_coefficients hv AA K β hβ hAK f hf hgood hg
  have h0 : (fun j => b j 0) = 0 := eq_zero_of_sum_mul_coset_eq_zero (v := v) K β hβ f hgood 0 _ (fun k => by
    have e : g (k : N) = 0 := by simpa [resK] using congrFun hres k
    calc ∑ j, b j 0 * f j (0 + k) = ∑ j, b j (0 + k) * f j (0 + k) :=
          Finset.sum_congr rfl fun j _ => by rw [hbinv j 0 k]
      _ = g (0 + k) := by rw [hgb]; simp [Finset.sum_apply]
      _ = 0 := by rw [zero_add]; exact e)
  rw [hgb]
  exact Submodule.sum_mem _ fun j _ => Submodule.mul_mem_mul
    (mem_map_augmentationIdeal_comap_pullbackQuotient AA K (hbA j) (hbinv j) (by simpa using congrFun h0 j)) (hf j)
end ReciprocityTheory.PGsh.L2
