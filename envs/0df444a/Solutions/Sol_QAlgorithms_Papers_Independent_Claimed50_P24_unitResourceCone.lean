-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P24.unitResourceCone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:23:52.881067+00:00
-- url     : https://prove2.me/submissions/5292960b-4c95-4b9e-86aa-4952f5f27ec5

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P24
noncomputable section

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Claimed50.P24

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel erasureDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I B E J D F : Type}

variable [Fintype I] [Fintype B] [Fintype E] [Fintype J] [Fintype D] [Fintype F]

variable [DecidableEq I] [DecidableEq B] [DecidableEq E]

variable [DecidableEq J] [DecidableEq D] [DecidableEq F]

variable [Nonempty I] [Nonempty B] [Nonempty E]

variable [Nonempty J] [Nonempty D] [Nonempty F]

/-- Section 4, PDF p.6: exact algebraic unit resource achievable cone, not a converse
for all possible noiseless protocols. No nonnegativity assumption on the net rates. -/
theorem solution :
    unitCone = {r | r 0 + r 1 ≤ 0 ∧ r 0 + r 1 + r 2 ≤ 0 ∧ r 1 + r 2 ≤ 0} := by
  ext r
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, rfl⟩
    simp only [Set.mem_setOf_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨h1, h2, h3⟩
    refine ⟨-(r 0 + r 1), -(r 0 + r 1 + r 2), -(r 1 + r 2), by linarith, by linarith, by linarith, ?_⟩
    ext i
    fin_cases i <;> simp <;> ring


end
