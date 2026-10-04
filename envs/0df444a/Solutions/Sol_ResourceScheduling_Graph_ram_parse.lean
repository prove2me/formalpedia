-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_parse
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:51:12.335579+00:00
-- url     : https://prove2.me/submissions/63bebfe7-c74e-457d-a150-ed9f2d234572

import Definitions.Def_ResourceScheduling_Graph_RAMParse
import Theorems.Thm_ResourceScheduling_Graph_split_ones
import Theorems.Thm_ResourceScheduling_Graph_stack_prefix
import Theorems.Thm_CookPvsNP_stack_basic_macros

set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (t good : V) (hne : t ≠ good) :
    StackImplements RAMRep (ramParse t good) (ramParseState t good)
      (fun s => 3 * s.val t + 3 * s.val good + 3 * s.word.length + 7) := by
  intro s l hr
  let n := (splitOnes s.word).1
  let rest := (splitOnes s.word).2
  let l1 := Function.update l (ramReg t) []
  let l2 := Function.update l1 (ramReg good) []
  let l3 := Function.update (Function.update l2 ramInput rest) (ramReg t) (List.replicate n Letter.one)
  let w := if rest = [] then [] else [Letter.one]
  let l4 := Function.update (Function.update l3 ramInput rest.tail) (ramReg good) w
  have hs := split_ones s.word
  have h2i : l2 ramInput = s.word := by simpa [l2, l1, ramReg, ramInput] using hr.2.1
  have h2t : l2 (ramReg t) = [] := by simp [l2, l1, ramReg, hne]
  have hp := stack_prefix ramInput (ramReg t) (by simp [ramInput, ramReg]) n rest hs.2.1 l2
    (h2i.trans hs.1)
  simp only [h2t, List.append_nil] at hp
  let act := fun (h : RAMWire V → Option Letter) k =>
    if k = ramInput then StackAct.pop else
    if k = ramReg good ∧ (h ramInput).isSome then .push Letter.one else .keep
  have ha : StackProg.applyAct act l3 = l4 := by
    funext k
    by_cases hi : k = ramInput
    · subst k; simp [StackProg.applyAct, act, l3, l4, StackAct.apply, ramReg, ramInput]
    by_cases hg : k = ramReg good
    · subst k
      cases hrest : rest <;> simp [StackProg.applyAct, act, l4, l3, l2, l1, StackAct.apply,
        ramReg, ramInput, Ne.symm hne, w, hrest]
    · simp [StackProg.applyAct, act, l4, StackAct.apply, hi, hg]
  have he := ((stack_basic_macros (ramReg t) l).2.2).seq
    (((stack_basic_macros (ramReg good) l1).2.2).seq
      (hp.seq (StackProg.Exec.act act l3)))
  rw [ha] at he
  refine ⟨_, l4, ?_, he, ?_⟩
  · have hg : (l1 (ramReg good)).length = s.val good := by
      simpa [l1, ramReg, Ne.symm hne] using hr.1 good
    rw [hg, hr.1 t]; dsimp only
    have hn : n ≤ s.word.length := by dsimp [n]; omega
    omega
  · have hv (v : V) : (l (Sum.inl (Sum.inl v))).length = s.val v := hr.1 v
    have ht (j : Fin 6) : l (Sum.inl (Sum.inr j)) = [] := hr.2.2.2 j
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v
      by_cases hg : v = good
      · subst v
        by_cases hempty : (splitOnes s.word).2 = [] <;>
          simp [l4, w, ramParseState, RAMState.set, rest, hempty]
      by_cases hx : v = t
      · subst v
        simp [l4, l3, l2, l1, ramReg, ramInput, hne, ramParseState, RAMState.set, n]
      · simp [l4, l3, l2, l1, ramReg, ramInput, hg, hx, ramParseState, RAMState.set, hv]
    · simp [l4, ramReg, ramInput, ramParseState, rest]
    · simpa [l4, l3, l2, l1, ramReg, ramInput, ramOutput, ramParseState, RAMState.set]
        using hr.2.2.1
    · intro j
      simp [l4, l3, l2, l1, ramReg, ramInput, ramTmp, ht]

#print axioms solution
