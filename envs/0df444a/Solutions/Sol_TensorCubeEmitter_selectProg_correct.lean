-- Prove2me | solution 1 for TensorCubeEmitter.selectProg_correct
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:01:13.124552+00:00
-- url     : https://prove2.me/submissions/0d6e71dd-a6e4-4baa-ac16-032483b3ec3b

import Definitions.Def_TensorCubeEmitter
open CookPvsNP ProjSchedTW.Complexity
open TensorCubeEmitter

private theorem emit_correct (xs : List BSym) (p n o : List BSym) :
    (emitProg xs).Exec (store p n o) (store p n (xs ++ o)) (2 * xs.length + 1) := by
  induction xs with
  | nil =>
      have h : StackProg.applyAct (fun _ _ => StackAct.keep) (store p n o) = store p n o := by
        funext k
        rfl
      simpa only [emitProg, List.nil_append, List.length_nil, Nat.mul_zero, Nat.zero_add, h] using
        (StackProg.Exec.act (fun _ _ => StackAct.keep) (store p n o))
  | cons a xs ih =>
      have h : StackProg.applyAct (fun _ (k : Fin 3) => if k = 2 then StackAct.push a else StackAct.keep)
          (store p n (xs ++ o)) = store p n (a :: (xs ++ o)) := by
        funext k
        fin_cases k <;> simp [StackProg.applyAct, StackAct.apply, store]
      have he := StackProg.Exec.seq ih (StackProg.Exec.act (fun _ (k : Fin 3) => if k = 2 then StackAct.push a else StackAct.keep) (store p n (xs ++ o)))
      rw [h] at he
      simp only [emitProg, List.cons_append, List.length_cons]
      convert he using 1 <;> omega

theorem solution (positive negative : Bool) (positiveTail negativeTail output : List BSym) :
    ∃ steps, steps ≤ 13 ∧
      selectProg.Exec
        (store (flagSym positive :: positiveTail) (flagSym negative :: negativeTail) output)
        (store (flagSym positive :: positiveTail) (flagSym negative :: negativeTail)
          (TensorNP.Eigen.encRat (coefficient positive negative) ++ output)) steps := by
  cases positive <;> cases negative
  · refine ⟨9, by decide, ?_⟩
    change (StackProg.branch hasPositive _ _).Exec _ _ _
    have hp : hasPositive (fun k => (store (BSym.zero :: positiveTail) (BSym.zero :: negativeTail) output k).head?) = false := rfl
    have hn : hasNegative (fun k => (store (BSym.zero :: positiveTail) (BSym.zero :: negativeTail) output k).head?) = false := rfl
    exact StackProg.Exec.branchFalse hp (StackProg.Exec.branchFalse hn (emit_correct [BSym.sep, BSym.one, BSym.sep] _ _ output))
  · refine ⟨13, by decide, ?_⟩
    change (StackProg.branch hasPositive _ _).Exec _ _ _
    have hp : hasPositive (fun k => (store (BSym.zero :: positiveTail) (BSym.one :: negativeTail) output k).head?) = false := rfl
    have hn : hasNegative (fun k => (store (BSym.zero :: positiveTail) (BSym.one :: negativeTail) output k).head?) = true := rfl
    exact StackProg.Exec.branchFalse hp (StackProg.Exec.branchTrue hn (emit_correct [BSym.minus, BSym.one, BSym.sep, BSym.one, BSym.sep] _ _ output))
  · refine ⟨10, by decide, ?_⟩
    change (StackProg.branch hasPositive _ _).Exec _ _ _
    have hp : hasPositive (fun k => (store (BSym.one :: positiveTail) (BSym.zero :: negativeTail) output k).head?) = true := rfl
    exact StackProg.Exec.branchTrue hp (emit_correct [BSym.one, BSym.sep, BSym.one, BSym.sep] _ _ output)
  · refine ⟨10, by decide, ?_⟩
    change (StackProg.branch hasPositive _ _).Exec _ _ _
    have hp : hasPositive (fun k => (store (BSym.one :: positiveTail) (BSym.one :: negativeTail) output k).head?) = true := rfl
    exact StackProg.Exec.branchTrue hp (emit_correct [BSym.one, BSym.sep, BSym.one, BSym.sep] _ _ output)