-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.chain_lemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:59:18.475603+00:00
-- url     : https://prove2.me/submissions/4a26b225-1c02-4a9b-8135-c7957c4da560

import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
import Theorems.Thm_Scott1976_DataTypesAsLattices_exists_index_of_finset
import Theorems.Thm_Scott1976_DataTypesAsLattices_e_finite
import Theorems.Thm_Scott1976_DataTypesAsLattices_e_pow2
import Theorems.Thm_Scott1976_DataTypesAsLattices_isScottContinuous_monotone
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_1
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem



set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {f : Pomega → Pomega} (hf : IsScottContinuous f)
    (xs : ℕ → Pomega) (hmono : ∀ n, xs n ⊆ xs (n + 1)) :
    f (⋃ n, xs n) = ⋃ n, f (xs n) := by
  apply subset_antisymm
  · intro k hk
    have hchar := (theorem_1_1 f).mp hf (⋃ n, xs n) (2 ^ k)
    have hfin : e (2 ^ k) ⊆ f (⋃ n, xs n) := by
      simp [e_pow2, Set.singleton_subset_iff, hk]
    obtain ⟨m, hm, hkm⟩ := hchar.mp hfin
    have hwit : ∀ i ∈ e m, ∃ n, i ∈ xs n := by
      intro i hi
      obtain ⟨n, hix⟩ := Set.mem_iUnion.mp (hm hi)
      exact ⟨n, hix⟩
    obtain ⟨s, hs⟩ := (e_finite m).exists_finset_coe
    obtain ⟨N, hN⟩ := exists_index_of_finset xs hmono s (fun i hi =>
      hwit i (by
        have : i ∈ (s : Set ℕ) := hi
        rwa [hs] at this))
    have hem : e m ⊆ xs N := by rwa [← hs]
    refine Set.mem_iUnion.mpr ⟨N, ?_⟩
    have : e (2 ^ k) ⊆ f (xs N) :=
      subset_trans hkm (isScottContinuous_monotone hf hem)
    simpa [e_pow2, Set.singleton_subset_iff] using this
  · intro k hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
    exact isScottContinuous_monotone hf (Set.subset_iUnion xs n) hkn
end Scott1976.DataTypesAsLattices
