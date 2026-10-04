-- Prove2me | solution 1 for ResourceScheduling.Graph.stack_emit
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:18:23.161927+00:00
-- url     : https://prove2.me/submissions/7f8e7ad4-83a5-49b4-9b02-d85c9119b6c2

import Definitions.Def_ResourceScheduling_Graph_StackEmit
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_map_transfer
import Theorems.Thm_CookPvsNP_stack_basic_macros

set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution {K : Type} [DecidableEq K] (r : Fin 4 ↪ K)
    (s : K → List Letter) (h2 : s (r 2) = []) (h3 : s (r 3) = []) :
    (emitUnaryProg r).Exec s
      (Function.update s (r 1) (Letter.sep :: (List.replicate (s (r 0)).length Letter.one ++ s (r 1))))
      (9 * (s (r 0)).length + 7) := by
  have neq (i j : Fin 4) (h : i ≠ j) : r i ≠ r j := r.injective.ne h
  have eqs (i j : Fin 4) : (r i = r j) ↔ i = j := r.injective.eq_iff
  let s1 := Function.update s (r 2) (s (r 0))
  let s2 := Function.update s (r 1) (List.replicate (s (r 0)).length Letter.one ++ s (r 1))
  have hcopy := stack_copy (r 0) (r 2) (r 3)
    (neq _ _ (by decide)) (neq _ _ (by decide)) (neq _ _ (by decide)) s h3
  simp only [h2, List.append_nil] at hcopy
  have hm := stack_map_transfer (r 2) (fun k => decide (k = r 1)) (fun _ => Letter.one) s1
  have hf : mapTransferStore (r 2) (fun k => decide (k = r 1)) (fun _ => Letter.one) s1 = s2 := by
    funext k
    by_cases hk : k = r 1
    · subst k
      simp [s2, s1, mapTransferStore, eqs]
    by_cases hk' : k = r 2
    · subst k; simp [s2, s1, mapTransferStore, eqs, h2]
    · simp [s2, s1, mapTransferStore, Function.update, hk, hk']
  rw [hf] at hm
  have hp := (stack_basic_macros (r 1) s2).1 Letter.sep
  have hout : Function.update s2 (r 1) (Letter.sep :: s2 (r 1)) =
      Function.update s (r 1) (Letter.sep :: (List.replicate (s (r 0)).length Letter.one ++ s (r 1))) := by
    simp [s2]
  rw [hout] at hp
  have hprog := StackProg.Exec.seq hcopy (StackProg.Exec.seq hm hp)
  convert hprog using 1 <;> first | rfl | (simp only [s1, Function.update_self]; omega)

#print axioms solution
