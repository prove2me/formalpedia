-- Prove2me | solution 1 for Stallings.folded_recognizer_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:16:50.751796+00:00
-- url     : https://prove2.me/submissions/713f8dbc-7fcd-42e2-94fc-a016abbfa4bc

import Definitions.Def_Stallings
import Definitions.Def_Stallings_Solution
import Theorems.Thm_Stallings_InverseAutomaton_accepts_iff_mem_loopSubgroup
import Theorems.Thm_Stallings_InverseAutomaton_membershipTest_eq_true_iff
import Theorems.Thm_Stallings_foldWords_loopSubgroup_eq_generatorSubgroup
attribute [local simp] Stallings.InverseAutomaton.membershipTest_eq_true_iff


section
namespace Stallings
private theorem foldlRun_none {V : Type*} (G : InverseAutomaton V) (w : Word) :
    w.foldl (fun state letter => state.bind fun vertex => G.next vertex letter)
      none = none := by
  induction w with
  | nil => rfl
  | cons x xs ih => simp [List.foldl_cons, ih]
private theorem foldl_run_eq {V : Type*} (G : InverseAutomaton V) (v : V)
    (w : Word) :
    w.foldl (fun state letter => state.bind fun vertex => G.next vertex letter)
      (some v) = G.run v w := by
  induction w generalizing v with
  | nil => rfl
  | cons x xs ih =>
      cases hnext : G.next v x with
      | none => simp [List.foldl_cons, hnext, InverseAutomaton.run, foldlRun_none]
      | some u =>
          simpa [List.foldl_cons, hnext, InverseAutomaton.run] using ih (v := u)
end Stallings
end

set_option autoImplicit true
open Stallings
namespace Stallings
theorem _root_.solution (S : List (List (Fin 2 × Bool))) :
    completeStatement S := by
  classical
  unfold completeStatement
  refine ⟨FlowerVertex S, inferInstance, (foldWords S).base, (foldWords S).next,
    ?_, ?_⟩
  · intro v x w h
    simpa [letterInv] using (foldWords S).inverse_next h
  · intro g
    change (FreeGroup.toWord g).foldl
        (fun state letter => state.bind fun vertex => (foldWords S).next vertex letter)
        (some (foldWords S).base) = some (foldWords S).base ↔
      g ∈ generatorSubgroup S
    rw [foldl_run_eq (foldWords S) (foldWords S).base (FreeGroup.toWord g)]
    have hcorrect := InverseAutomaton.accepts_iff_mem_loopSubgroup (foldWords S) g
    have hrun : (foldWords S).run (foldWords S).base (FreeGroup.toWord g) =
        some (foldWords S).base ↔ g ∈ (foldWords S).loopSubgroup := by
      simpa [InverseAutomaton.accepts] using hcorrect
    rw [foldWords_loopSubgroup_eq_generatorSubgroup] at hrun
    exact hrun
end Stallings
