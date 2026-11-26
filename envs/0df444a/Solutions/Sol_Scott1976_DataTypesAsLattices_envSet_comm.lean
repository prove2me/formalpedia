-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.envSet_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:58:36.4464+00:00
-- url     : https://prove2.me/submissions/9cf7bf0a-6965-4e27-a15f-5454d000eeb8

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_ofNat
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem


attribute [local simp] Scott1976.DataTypesAsLattices.mem_ofNat

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {ρ : ℕ → Pomega} {i j : ℕ} (hij : i ≠ j) (v w : Pomega) :
    envSet (envSet ρ i v) j w = envSet (envSet ρ j w) i v := by
  funext k
  unfold envSet
  by_cases hj : k = j
  · subst hj
    simp [Function.update, hij.symm]
  · by_cases hi : k = i
    · subst hi
      simp [Function.update, hij]
    · simp [Function.update, hi, hj]
end Scott1976.DataTypesAsLattices
