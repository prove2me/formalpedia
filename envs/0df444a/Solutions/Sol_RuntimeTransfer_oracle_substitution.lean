-- Prove2me | solution 1 for RuntimeTransfer.oracle_substitution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T11:26:12.280364+00:00
-- url     : https://prove2.me/submissions/cf512387-bbc2-4dbf-b201-a4afcb12e78c

import Definitions.Def_RuntimeTransfer

set_option autoImplicit false
namespace RuntimeTransfer

end RuntimeTransfer

open RuntimeTransfer
theorem solution {Q A R : Type} (p : Program Q A R)
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

#print axioms solution
