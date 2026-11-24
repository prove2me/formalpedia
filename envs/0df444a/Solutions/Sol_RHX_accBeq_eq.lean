-- Prove2me | solution 1 for RHX.accBeq_eq
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:50:06.880937+00:00
-- url     : https://prove2.me/submissions/6de302ef-627d-47ac-9b09-d67b0cbb48ed

import Definitions.Def_RHX_RunChain
set_option maxRecDepth 100000
open ArbEcon.Off

namespace RHX

theorem accBeq_eq {x y : Acc} (h : accBeq x y = true) : x = y := by
  cases x; cases y
  simp only [accBeq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  subst h1 h2 h3 h4 h5 h6; rfl

theorem accsBeq_eq : ∀ {xs ys : List Acc}, accsBeq xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [accsBeq, Bool.and_eq_true] at h
    rw [accBeq_eq h.1, accsBeq_eq h.2]
  | [], _ :: _, h => by simp [accsBeq] at h
  | _ :: _, [], h => by simp [accsBeq] at h

theorem stoBeq_eq {s t : StO} (h : stoBeq s t = true) : s = t := by
  cases s; cases t
  simp only [stoBeq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  subst h1 h2 h3 h4; rw [accsBeq_eq h5]

theorem runO_succ (c : ArbEcon.Cfg) (o : OCfg) (n : Nat) (s : StO) :
    runO c o (n + 1) s = runO c o n (stepO c o s) := rfl

theorem runO_add (c : ArbEcon.Cfg) (o : OCfg) : ∀ (a b : Nat) (s : StO),
    runO c o (a + b) s = runO c o b (runO c o a s)
  | 0, b, s => by rw [Nat.zero_add]; rfl
  | a + 1, b, s => by
    rw [Nat.add_right_comm, runO_succ, runO_add c o a b (stepO c o s), runO_succ]

/-- Chaining two checked chunks. -/
theorem runO_chain (c : ArbEcon.Cfg) (o : OCfg) {a b : Nat} {s t u : StO}
    (h1 : runO c o a s = t) (h2 : runO c o b t = u) : runO c o (a + b) s = u := by
  rw [runO_add, h1, h2]

end RHX
open ArbEcon.Off RHX in
theorem solution {x y : Acc} (h : accBeq x y = true) : x = y := by
  apply RHX.accBeq_eq <;> assumption
