-- Prove2me | solution 1 for Verification.IntervalContracts.every_checked_row_is_sound
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T20:20:34.015265+00:00
-- url     : https://prove2.me/submissions/a8cd09f6-5b3f-44de-82f1-523460fad985

import Definitions.Def_ReusableIntervalContracts

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Verification.IntervalContracts

variable {S : Type*}

private theorem repeat_preservation (step : S → S) {P : S → Prop} (d : ℕ)
    (preserves : ∀ s, P s → P (step^[d] s)) (n : ℕ) {s : S}
    (starts : P s) : P (step^[n*d] s) := by
  induction n with
  | zero => simpa using starts
  | succ n ih =>
    rw [Nat.succ_mul, Nat.add_comm, Function.iterate_add_apply]
    exact preserves _ ih

/-- The DAG checks each row once as an obligation on any entry state.
Earlier rows may be reused at many unrelated positions of the run. -/
theorem checked_sound (m : Model S) (code : Table) (valid : Checked m code)
    (i : ℕ) (present : i < code.length) : Holds m.step m.pred (out code i) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro s begins
    let row := out code i
    let left := out code (first row)
    let right := out code (second row)
    have checked := valid i present s
    dsimp only [obligation, obligationAt] at checked
    change m.pred (post row) (m.step^[span row] s)
    change m.pred (pre row) s at begins
    by_cases identity : kind (out code i) = 0
    · simp only [identity, if_true] at checked
      rw [checked.1]
      exact checked.2 begins
    simp only [identity, if_false] at checked
    by_cases single : kind (out code i) = 1
    · simp only [single, if_true] at checked
      rw [checked.1]
      exact checked.2 trivial begins
    simp only [single, if_false] at checked
    by_cases atom : kind (out code i) = 2
    · simp only [atom, if_true] at checked
      exact m.primitive_sound _ checked s begins
    simp only [atom, if_false] at checked
    by_cases concat : kind (out code i) = 3
    · simp only [concat, if_true] at checked
      obtain ⟨aBefore,bBefore,duration,inputEq,interfaceEq,outputEq⟩ := checked
      have a := ih (first row) aBefore (aBefore.trans present)
      have b := ih (second row) bBefore (bBefore.trans present)
      have arrive : m.pred (post left) (m.step^[span left] s) := a s (inputEq ▸ begins)
      have back := b (m.step^[span left] s) (interfaceEq ▸ arrive)
      rw [duration, Nat.add_comm, Function.iterate_add_apply, ← outputEq]
      exact back
    simp only [concat, if_false] at checked
    by_cases loop : kind (out code i) = 4
    · simp only [loop, if_true] at checked
      obtain ⟨earlier,duration,inputEq,loopEq,outputEq⟩ := checked
      have contract := ih (first row) earlier (earlier.trans present)
      have preserves : ∀ s, m.pred (pre left) s → m.pred (pre left) (m.step^[span left] s) := by
        intro s hs
        exact loopEq ▸ contract s hs
      rw [duration, outputEq]
      exact repeat_preservation m.step (span left) preserves (second row) (inputEq ▸ begins)
    simp only [loop, if_false] at checked
    by_cases weaken : kind (out code i) = 5
    · simp only [weaken, if_true] at checked
      obtain ⟨earlier,duration,entry,_⟩ := checked
      have checkedAfter := valid i present (m.step^[span left] s)
      have child := ih (first row) earlier (earlier.trans present)
      have arrives : m.pred (post left) (m.step^[span left] s) := child s (entry begins)
      simp [obligation, obligationAt, weaken] at checkedAfter
      rw [duration]
      exact checkedAfter.2.2.2 arrives
    simp only [weaken, if_false] at checked
    by_cases casesRule : kind (out code i) = 6
    · simp only [casesRule, if_true] at checked
      obtain ⟨aBefore,bBefore,aLen,bLen,aOut,bOut,oneSide⟩ := checked
      rcases oneSide begins with onLeft | onRight
      · have contract := ih (first row) aBefore (aBefore.trans present)
        rw [aLen, ← aOut]
        exact contract s onLeft
      · have contract := ih (second row) bBefore (bBefore.trans present)
        rw [bLen, ← bOut]
        exact contract s onRight
    rw [if_neg casesRule] at checked
    exact checked.elim

end Verification.IntervalContracts

open Verification.IntervalContracts

theorem solution {S : Type*} (model : Model S) (code : Table)
    (checked : Checked model code) (i : ℕ) (present : i < code.length) :
    Holds model.step model.pred (out code i) := by
  exact checked_sound model code checked i present

#print axioms solution
