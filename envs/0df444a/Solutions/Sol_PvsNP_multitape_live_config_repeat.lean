-- Prove2me | solution 1 for PvsNP.multitape_live_config_repeat
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T10:06:58.80306+00:00
-- url     : https://prove2.me/submissions/ec59edb9-c6c8-48fa-b669-1379774c93e8

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

private theorem halt_flag (d : Desc) (x : List ℕ) (t : ℕ) :
    (simulate d x t).2 = (((fun c : SCfg => (step d x c).1)^[t]) (init d)).state.isNone := by
  have project (i : ℕ) : ((stepOut d x)^[i] (init d,[])).1 =
      ((fun c : SCfg => (step d x c).1)^[i]) (init d) := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
      exact congrArg (fun c => (step d x c).1) ih
  exact congrArg (fun c : SCfg => c.state.isNone) (project t)

theorem solution (d : Desc) (x : List ℕ) {u v : ℕ} (order : u < v)
    (live : (simulate d x v).2 = false)
    (repeatConfig : ((fun c : SCfg => (step d x c).1)^[u]) (init d) =
      ((fun c : SCfg => (step d x c).1)^[v]) (init d)) :
    ∀ t, (simulate d x t).2 = false := by
  have noHalt : ¬ ∃ t, (simulate d x t).2 = true := by
    intro existsHalt
    let T := Nat.find existsHalt
    have stopped : (simulate d x T).2 = true := Nat.find_spec existsHalt
    have before : v < T := by
      by_contra! after
      rw [halted_stays d x stopped after, stopped] at live
      cases live
    let f (c : SCfg) := (step d x c).1
    change f^[u] (init d) = f^[v] (init d) at repeatConfig
    have same : f^[T-v+u] (init d) = f^[T] (init d) := by
      calc
        _ = f^[T-v+v] (init d) := by
          simp only [Function.iterate_add_apply]
          exact congrArg (f^[T-v]) repeatConfig
        _ = _ := congrArg (fun i => f^[i] (init d)) (by omega)
    have earlyHalt : (simulate d x (T-v+u)).2 = true := by
      rw [halt_flag]
      change (f^[T-v+u] (init d)).state.isNone = true
      rw [same]
      exact (halt_flag d x T).symm.trans stopped
    exact (Nat.find_min existsHalt (show T-v+u < T by omega)) earlyHalt
  intro t
  exact Bool.eq_false_iff.mpr (fun contrary => noHalt ⟨t,contrary⟩)
