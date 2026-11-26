-- Prove2me | solution 1 for PvsNP.multitape_halted_output_prefix
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T10:07:01.823408+00:00
-- url     : https://prove2.me/submissions/421c9d97-6b9f-4e7a-8895-d5565630ae96

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Basic
import Mathlib

open Turing.MultiTapeTM.Universal

private theorem halted_stays (d : Desc) (x : List ℕ) {s t : ℕ}
    (halted : (simulate d x s).2 = true) (order : s ≤ t) :
    simulate d x t = simulate d x s := by
  unfold simulate at *
  generalize run : (stepOut d x)^[s] (init d, []) = c at *
  have stopped : c.1.state = none := by simpa using halted
  have fixed : stepOut d x c = c := by simp [stepOut, step, stopped]
  rw [show t = (t-s)+s by omega, Function.iterate_add_apply,run]
  exact congrArg (fun q : SCfg × List ℕ => (q.2,q.1.state.isNone))
    (Function.iterate_fixed fixed (t-s))

private theorem output_prefix (d : Desc) (x : List ℕ) {s t : ℕ} (order : s ≤ t) :
    (simulate d x s).1 <+: (simulate d x t).1 := by
  induction order with
  | refl => exact List.prefix_rfl
  | @step t _ ih =>
    apply ih.trans
    let run := (stepOut d x)^[t] (init d,[])
    have next : (stepOut d x)^[t+1] (init d,[]) = stepOut d x run :=
      Function.iterate_succ_apply' ..
    simp only [simulate,next]
    exact List.prefix_append _ _

theorem solution (d : Desc) (x output : List ℕ) {t : ℕ}
    (finished : simulate d x t = (output,true)) :
    ∀ s, ((simulate d x s).1 <+: output) ∧
      ((simulate d x s).2 = true → simulate d x s = (output,true)) := by
  have halted : (simulate d x t).2 = true := congrArg Prod.snd finished
  intro s
  rcases le_total s t with early | late
  · refine ⟨?_,fun stopped => (halted_stays d x stopped early).symm.trans finished⟩
    have prior := output_prefix d x early
    rwa [finished] at prior
  · have same := (halted_stays d x halted late).trans finished
    exact ⟨by rw [same],fun _ => same⟩
