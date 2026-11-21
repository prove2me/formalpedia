-- Prove2me | solution 1 for StableMSR.Recovery.Compiler.BoundedSum.bounded_while_execution
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T18:10:06.139369+00:00
-- url     : https://prove2.me/submissions/c68259c3-9ffd-4889-9792-84a1dcab89bc

import Definitions.Def_StableMSR_BoundedSumRAM
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.BoundedSum
open Polynomial
set_option maxHeartbeats 1600000
open scoped Classical

theorem solution {n : ℕ} (d : Point n→Point n→ℝ) (c : Cmd) (guard : Cond) (A : ℕ→Store→Prop)
    (N B : ℕ) (h : LoopBound d c guard A N B) (i : ℕ) (hi : i ≤ N) (s : Store) (hs : A i s) :
    ∃t z, Executes d (.whileDo guard c) s t z ∧ z ≤ (N-i)*(B+2)+2 ∧ A N t := by
  have finishLoop (r j : ℕ) (eq : j+r=N) (s : Store) (hs : A j s) :
      ∃t z, Executes d (.whileDo guard c) s t z ∧ z ≤ r*(B+2)+2 ∧ A N t := by
    induction r generalizing j s with
    | zero =>
      have e : j=N := by omega
      subst j
      exact ⟨s,2,.while_false (fun h' => (Nat.lt_irrefl N) ((h.1 N s hs).mp h')),by simp,hs⟩
    | succ r ih =>
      have lt : j < N := by omega
      obtain ⟨u,k,hk,bk,hu⟩ := h.2 j lt s hs
      obtain ⟨t,l,hl,bl,ht⟩ := ih (j+1) (by omega) u hu
      exact ⟨t,_,.while_true ((h.1 j s hs).mpr lt) hk hl,by rw [Nat.succ_mul];omega,ht⟩
  exact finishLoop (N-i) i (by omega) s hs

