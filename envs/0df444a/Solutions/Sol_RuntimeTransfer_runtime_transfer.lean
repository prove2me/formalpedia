-- Prove2me | solution 1 for RuntimeTransfer.runtime_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T11:26:12.697656+00:00
-- url     : https://prove2.me/submissions/0bb03cac-e1b7-4f48-9631-58ca47eb6c2c

import Mathlib.Order.Monotone.Basic
import Definitions.Def_RuntimeTransfer

set_option autoImplicit false
namespace RuntimeTransfer

theorem oracle_substitution {Q A R : Type} (p : Program Q A R)
    (spec : Q → A) (oracle : Q → A × ℕ) (bound : Q → ℕ)
    (hcorrect : ∀ q, (oracle q).1 = spec q)
    (hcost : ∀ q, (oracle q).2 ≤ bound q) :
    (p.run oracle).1 = p.value spec ∧
      (p.run oracle).2 ≤ p.budget spec bound := by
  induction p with
  | done r => exact ⟨rfl, le_rfl⟩
  | work c p ih =>
    exact ⟨ih.1, Nat.add_le_add_left ih.2 c⟩
  | query q next ih =>
    simp only [Program.run, Program.value, Program.budget, hcorrect q]
    exact ⟨(ih (spec q)).1, Nat.add_le_add (hcost q) (ih (spec q)).2⟩

theorem budget_bound {Q A R : Type} (p : Program Q A R)
    (spec : Q → A) (size : Q → ℕ) (T : ℕ → ℕ) (s : ℕ)
    (hT : Monotone T) (hs : p.QueriesBounded spec size s) :
    p.budget spec (fun q => T (size q)) ≤
      p.overhead spec + p.calls spec * T s := by
  induction p with
  | done r => simp [Program.budget, Program.overhead, Program.calls]
  | work c p ih =>
    simpa only [Program.budget, Program.overhead, Program.calls, Nat.add_assoc]
      using Nat.add_le_add_left (ih hs) c
  | query q next ih =>
    have h := Nat.add_le_add (hT hs.1) (ih (spec q) hs.2)
    simpa only [Program.budget, Program.overhead, Program.calls, Nat.add_mul,
      Nat.one_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

end RuntimeTransfer

open RuntimeTransfer
theorem solution {Q A R : Type} (p : Program Q A R)
    (spec : Q → A) (oracle : Q → A × ℕ) (size : Q → ℕ)
    (T : ℕ → ℕ) (s k h : ℕ)
    (hcorrect : ∀ q, (oracle q).1 = spec q)
    (hcost : ∀ q, (oracle q).2 ≤ T (size q))
    (hT : Monotone T) (hs : p.QueriesBounded spec size s)
    (hk : p.calls spec ≤ k) (hh : p.overhead spec ≤ h) :
    (p.run oracle).1 = p.value spec ∧ (p.run oracle).2 ≤ h + k * T s := by
  obtain ⟨hc, ht⟩ := oracle_substitution p spec oracle (fun q => T (size q)) hcorrect hcost
  exact ⟨hc, ht.trans ((budget_bound p spec size T s hT hs).trans
    (Nat.add_le_add hh (Nat.mul_le_mul_right (T s) hk)))⟩

#print axioms solution
