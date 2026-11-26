-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.omega_first_recursion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:01:05.803004+00:00
-- url     : https://prove2.me/submissions/700f9180-0e5d-4711-aa03-0f6b85900f0f

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_ofNat
import Theorems.Thm_Scott1976_DataTypesAsLattices_omegaComb_app
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e_lt
import Theorems.Thm_Scott1976_DataTypesAsLattices_funOf_diag_iUnion
import Theorems.Thm_Scott1976_DataTypesAsLattices_isScottContinuous_monotone
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_pair_le_left
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_2_i
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_4
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem


attribute [local simp] Scott1976.DataTypesAsLattices.mem_ofNat

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    funOf (omegaComb (graph f)) (omegaComb (graph f)) = fix f := by
  let d := omegaComb (graph f)
  have hd : ∀ x, funOf d x = f (funOf x x) := by
    intro x
    simp [d, omegaComb_app, theorem_1_2_i hf]
  have hθ : funOf d d = f (funOf d d) := hd d
  refine subset_antisymm ?_ ((theorem_1_4 hf).2 _ hθ.symm)
  intro m hm
  -- Scott's argument: reduce to `e_l ⊆ d → e_l ⬝ e_l ⊆ a` with `a = fix f`.
  let a := fix f
  have ha : f a = a := (theorem_1_4 hf).1
  have key : ∀ l, e l ⊆ d → funOf (e l) (e l) ⊆ a := by
    intro l
    induction l using Nat.strongRecOn with
    | ind l ih =>
      intro hld k hk
      obtain ⟨n, hn, hp⟩ := hk
      have hnlt : n < l := (pair_le_left n k).trans_lt (mem_e_lt hp)
      have hnd : e n ⊆ d := subset_trans hn hld
      have hna : funOf (e n) (e n) ⊆ a := ih n hnlt hnd
      -- `(n,k) ∈ e_l ⊆ d = λx. f(x x)`, so `k ∈ f(e n ⬝ e n)`
      have : k ∈ funOf d (e n) := ⟨n, subset_rfl, hld hp⟩
      have : k ∈ f (funOf (e n) (e n)) := by
        rwa [hd] at this
      have : k ∈ f a := isScottContinuous_monotone hf hna this
      rwa [ha] at this
  rw [funOf_diag_iUnion] at hm
  obtain ⟨l, hl, hml⟩ := Set.mem_iUnion.mp hm
  exact key l hl hml
end Scott1976.DataTypesAsLattices
