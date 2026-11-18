-- Prove2me | solution 1 for StudentTeacher976.Adaptivity.padded_residual_verifier
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T01:41:11.085561+00:00
-- url     : https://prove2.me/submissions/c6cc6194-1fd8-4e33-96e1-76eec7b379ba

import Theorems.Thm_StudentTeacher976_Adaptivity_finite_control_compilation
import Theorems.Thm_StudentTeacher976_Adaptivity_padded_residual_program
set_option autoImplicit false
open QAdvFew.PoQOracle
open StudentTeacher976.Adaptivity

theorem solution (V : OTM) (clock : Polynomial ℕ) (ps : List (Polynomial ℕ))
    (htotal : ∀ s : Word, (V.result (fun _ => false) s (clock.eval s.length)).isSome) :
    ∃ M : OTM, ∃ bound : Polynomial ℕ,
      (∀ s : Word, (M.result (fun _ => false) s (bound.eval s.length)).isSome) ∧
      ∀ (s : Word) (ys : List Word),
        M.result (fun _ => false) (tup (s :: ys)) (bound.eval (tup (s :: ys)).length) = some true ↔
          ∃ x y : Word, s = tup [x, y] ∧
            ¬ V.result (fun _ => false)
              (tup (x :: y :: List.zipWith (fun n w => w.take n) (ps.map fun p => p.eval x.length) ys))
              (clock.eval (tup (x :: y :: List.zipWith (fun n w => w.take n)
                (ps.map fun p => p.eval x.length) ys)).length) = some true := by
  obtain ⟨Q, A, hQ, hA, P, bound, hhalt, hcorrect⟩ := padded_residual_program V clock ps htotal
  letI : Fintype Q := hQ
  letI : Fintype A := hA
  obtain ⟨M, hM⟩ := finite_control_compilation P
  refine ⟨M, 3*bound+1, ?_, ?_⟩
  · intro s
    obtain ⟨b, hb⟩ := hhalt s
    have hres := (hM (fun _ => false) s (bound.eval s.length) b hb).1
    simpa using congrArg Option.isSome hres
  · intro s ys
    have heval : (3*bound+1).eval (tup (s::ys)).length = 3*bound.eval (tup (s::ys)).length+1 := by simp
    rw [heval]
    have hequiv : M.result (fun _ => false) (tup (s::ys))
        (3*bound.eval (tup (s::ys)).length+1) = some true ↔
        ((P.step (fun _ => false))^[bound.eval (tup (s::ys)).length]
          (P.initial (tup (s::ys)))).state = Sum.inl true := by
      obtain ⟨b, hb⟩ := hhalt (tup (s::ys))
      have hres := (hM (fun _ => false) (tup (s::ys)) (bound.eval (tup (s::ys)).length) b hb).1
      rw [hres, hb]
      cases b <;> simp
    exact hequiv.trans (hcorrect s ys)
