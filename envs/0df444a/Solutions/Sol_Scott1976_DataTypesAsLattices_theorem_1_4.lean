-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_1_4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:59:54.104017+00:00
-- url     : https://prove2.me/submissions/a09bf41e-f7b9-4e7b-875d-a6f463d8d6e9

import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
import Theorems.Thm_Scott1976_DataTypesAsLattices_chain_lemma
import Theorems.Thm_Scott1976_DataTypesAsLattices_iterateBot_mono
import Theorems.Thm_Scott1976_DataTypesAsLattices_isScottContinuous_monotone
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem



set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    f (fix f) = fix f ∧ ∀ x, f x = x → fix f ⊆ x := by
  constructor
  · -- f(fix f) = ⋃ f(fⁿ(∅)) = ⋃ fⁿ⁺¹(∅) = fix f
    have hchain := chain_lemma hf (iterateBot f) (iterateBot_mono hf)
    unfold fix
    rw [hchain]
    ext k
    constructor
    · intro hk
      obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
      exact Set.mem_iUnion.mpr ⟨n + 1, hkn⟩
    · intro hk
      obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
      cases n with
      | zero => simp [iterateBot, botElem] at hkn
      | succ n => exact Set.mem_iUnion.mpr ⟨n, hkn⟩
  · intro x hx k hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
    have hsub : ∀ n, iterateBot f n ⊆ x := by
      intro n
      induction n with
      | zero => simp [iterateBot, botElem]
      | succ n ih =>
        simpa [iterateBot, hx] using isScottContinuous_monotone hf ih
    exact hsub n hkn
end Scott1976.DataTypesAsLattices
