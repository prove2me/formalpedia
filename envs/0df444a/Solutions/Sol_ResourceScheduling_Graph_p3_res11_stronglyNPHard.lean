-- Prove2me | solution 1 for ResourceScheduling.Graph.p3_res11_stronglyNPHard
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T17:05:46.272345+00:00
-- url     : https://prove2.me/submissions/d5b28372-8574-4911-a519-cc71cebf44ea

import Definitions.Def_ResourceScheduling_Graph_WordReduction
import Theorems.Thm_ResourceScheduling_Graph_encQ2_injective
import Theorems.Thm_ResourceScheduling_Graph_graph_decoder_correct
import Theorems.Thm_ResourceScheduling_Graph_triangles_iff_p3Schedule
import Theorems.Thm_ResourceScheduling_Graph_reduceWord_polyTime
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_polyTimeComputable_comp
import Theorems.Thm_CookPvsNP_polyReducible_trans

set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

private def dropProgram (A : Type) : ℕ → StackProg Unit A
  | 0 => .act (fun _ _ => .keep)
  | n + 1 => .seq (.act (fun _ _ => .pop)) (dropProgram A n)

private theorem drop_exec {A : Type} (n : ℕ) (s : Unit → List A) :
    (dropProgram A n).Exec s (fun i => (s i).drop n) (2 * n + 1) := by
  induction n generalizing s with
  | zero =>
    change StackProg.Exec (.act (fun _ _ => .keep)) s s 1
    exact StackProg.Exec.act (fun _ _ => StackAct.keep) s
  | succ n ih =>
    have h := (StackProg.Exec.act (fun _ _ => StackAct.pop) s).seq
      (ih (StackProg.applyAct (fun _ _ => StackAct.pop) s))
    simpa [dropProgram, StackProg.applyAct, StackAct.apply, List.drop_tail,
      Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Removing any fixed number of initial letters is polynomial-time computable
in the original Cook single-tape model, including on words shorter than that number. -/
private theorem drop_polyTime_aux {A : Type} [Fintype A] [DecidableEq A] (n : ℕ) :
    PolyTimeComputable (fun w : List A => w.drop n) := by
  apply stack_program_polytime (dropProgram A n) () () _ (2 * n + 1)
  intro w
  refine ⟨fun _ => w.drop n, 2 * n + 1, by omega, ?_, rfl⟩
  simpa using drop_exec n (fun _ : Unit => w)

private theorem encP3_injective : Function.Injective encP3 := by
  intro x y h
  have he : encQ2 (![2, 1], x) = encQ2 (![2, 1], y) := by
    change unary 2 ++ unary 1 ++ encP3 x = unary 2 ++ unary 1 ++ encP3 y
    rw [h]
  exact congrArg Prod.snd (encQ2_injective he)

private theorem drop_speed_prefix (x : ResDot11Data) :
    (encQ2 (![2, 1], x)).drop 5 = encP3 x := by
  simp [encQ2, encP3, unary, List.replicate_succ, List.append_assoc]

private theorem reduced_yes (d : GraphData) :
    P3Yes (reduce d) ↔ PartitionIntoTriangles d.G := by
  exact (triangles_iff_p3Schedule d).symm

private theorem empty_not_P3 : [] ∉ codeLang P3Yes encP3 := by
  rintro ⟨x, _, he⟩
  have h := congrArg List.length he
  simp [encP3, ResDot11Data.enc, unary] at h

private theorem word_correct (w : List Letter) :
    w ∈ trianglesLang ↔ (reduceWord w).drop 5 ∈ codeLang P3Yes encP3 := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    have he : (reduceWord (encGraph d)).drop 5 = encP3 (reduce d) := by
      simp only [reduceWord, graph_decoder_correct.1 d, drop_speed_prefix]
    rw [he]
    exact ⟨reduce d, (reduced_yes d).mpr hd, rfl⟩
  · intro h
    cases hd : decodeGraph w with
    | none =>
      have he : (reduceWord w).drop 5 = [] := by simp [reduceWord, hd]
      rw [he] at h
      exact False.elim (empty_not_P3 h)
    | some d =>
      rcases h with ⟨x, hx, he⟩
      have hcode : encP3 (reduce d) = encP3 x := by
        simpa only [reduceWord, hd, drop_speed_prefix] using he
      have hx' : x = reduce d := (encP3_injective hcode).symm
      subst x
      exact ⟨d, (reduced_yes d).mp hx, (graph_decoder_correct.2 w d hd).symm⟩

/-- The original milestone 3, retaining exactly its cited source-hardness hypothesis. -/
theorem solution (hT : NPHard trianglesLang) : StronglyNPHard P3Yes encP3 := by
  change NPHard (codeLang P3Yes encP3)
  have ht : PolyTimeComputable (fun w => (reduceWord w).drop 5) :=
    polyTimeComputable_comp reduceWord (fun w => w.drop 5)
      reduceWord_polyTime (drop_polyTime_aux 5)
  intro Sym _ _ L hL
  exact polyReducible_trans (hT Sym L hL) ⟨_, ht, word_correct⟩

#print axioms solution
