-- Prove2me | solution 1 for StudentTeacher976.Adaptivity.padded_residual_program
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T02:34:43.655764+00:00
-- url     : https://prove2.me/submissions/c4863ecf-179f-4ea6-9de6-da7e7b03fe39

import Theorems.Thm_StudentTeacher976_Adaptivity_multitape_decider_program
import Theorems.Thm_StudentTeacher976_Adaptivity_padded_residual_multitape
set_option autoImplicit false
open QAdvFew.PoQOracle
open QAdvFew.PoQOracle.OTM.FiniteControl
open StudentTeacher976.Adaptivity

theorem solution (V : OTM) (clock : Polynomial ℕ) (ps : List (Polynomial ℕ))
    (htotal : ∀ s : Word, (V.result (fun _ => false) s (clock.eval s.length)).isSome) :
    ∃ (Q A : Type) (_ : Fintype Q) (_ : Fintype A), ∃ P : Program Q A, ∃ bound : Polynomial ℕ,
      (∀ s : Word, ∃ b : Bool,
        ((P.step (fun _ => false))^[bound.eval s.length] (P.initial s)).state = Sum.inl b) ∧
      ∀ (s : Word) (ys : List Word),
        ((P.step (fun _ => false))^[bound.eval (tup (s :: ys)).length]
          (P.initial (tup (s :: ys)))).state = Sum.inl true ↔
          ∃ x y : Word, s = tup [x, y] ∧
            ¬ V.result (fun _ => false)
              (tup (x :: y :: List.zipWith (fun n w => w.take n) (ps.map fun p => p.eval x.length) ys))
              (clock.eval (tup (x :: y :: List.zipWith (fun n w => w.take n)
                (ps.map fun p => p.eval x.length) ys)).length) = some true := by
  obtain ⟨k, S, hS, M, bound, hhalt, hcorrect⟩ := padded_residual_multitape V clock ps htotal
  letI : Fintype S := hS
  obtain ⟨Q, A, hQ, hA, P, p, hP⟩ := multitape_decider_program M bound hhalt
  refine ⟨Q, A, hQ, hA, P, p, ?_, ?_⟩
  · intro s
    exact ⟨_, hP s⟩
  · intro s ys
    rw [hP]
    simpa only [Sum.inl.injEq] using hcorrect s ys
