-- Prove2me | solution 1 for TwoAgentSched.TotalTotal.ParseCompare.correct_and_total
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T20:43:08.486235+00:00
-- url     : https://prove2.me/submissions/79912f59-645b-4e9e-80df-35c7ea0697f3

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_ParseCompare
import Theorems.Thm_StackProgPortLift_liftProgC_exec
import Theorems.Thm_CookPvsNP_CanonicalBlockParser_execution_and_bounds
import Theorems.Thm_TwoAgentSched_TotalTotal_StackCompareDigits_correct_and_total

set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace StackProgPortLift

private theorem write_at_local {K L A : Type} (r : K ↪ L) (t : K → List A)
    (s : L → List A) (k : K) : write r t s (r k) = t k := by
  classical
  unfold write
  split
  · rename_i h
    have hk : Classical.choose h = k := r.injective (Classical.choose_spec h)
    rw [hk]
  · rename_i h
    exact (h ⟨k, rfl⟩).elim

private theorem write_outside_local {K L A : Type} (r : K ↪ L) (t : K → List A)
    (s : L → List A) {l : L} (h : ∀ k, r k ≠ l) : write r t s l = s l := by
  classical
  unfold write
  split
  · rename_i hex
    obtain ⟨k, hk⟩ := hex
    exact (h k hk).elim
  · rfl


end StackProgPortLift

namespace TwoAgentSched.TotalTotal.ParseCompare

open StackProgPortLift CookPvsNP.CanonicalBlockParser TwoAgentSched.TotalTotal.StackCompareDigits

private theorem leftInverse_correct (l : Fin 5) (k : Fin 3) :
    leftInverse l = some k ↔ leftPorts k = l := by fin_cases l <;> fin_cases k <;> decide
private theorem rightInverse_correct (l : Fin 5) (k : Fin 3) :
    rightInverse l = some k ↔ rightPorts k = l := by fin_cases l <;> fin_cases k <;> decide
private theorem compareInverse_correct (l : Fin 5) (k : Fin 3) :
    compareInverse l = some k ↔ comparePorts k = l := by fin_cases l <;> fin_cases k <;> decide

private theorem write_left (a b c input left right status result : List BSym) :
    write leftPorts (CookPvsNP.CanonicalBlockParser.store a b c) (store5 input left right status result) =
      store5 a b right c result := by
  funext k
  fin_cases k
  · simpa [leftPorts, CookPvsNP.CanonicalBlockParser.store, store5] using
      (StackProgPortLift.write_at_local leftPorts (CookPvsNP.CanonicalBlockParser.store a b c)
        (store5 input left right status result) (0 : Fin 3))
  · simpa [leftPorts, CookPvsNP.CanonicalBlockParser.store, store5] using
      (StackProgPortLift.write_at_local leftPorts (CookPvsNP.CanonicalBlockParser.store a b c)
        (store5 input left right status result) (1 : Fin 3))
  · have ho : ∀ j : Fin 3, leftPorts j ≠ (2 : Fin 5) := by intro j; fin_cases j <;> decide
    simpa [store5] using StackProgPortLift.write_outside_local leftPorts
      (CookPvsNP.CanonicalBlockParser.store a b c) (store5 input left right status result) ho
  · simpa [leftPorts, CookPvsNP.CanonicalBlockParser.store, store5] using
      (StackProgPortLift.write_at_local leftPorts (CookPvsNP.CanonicalBlockParser.store a b c)
        (store5 input left right status result) (2 : Fin 3))
  · have ho : ∀ j : Fin 3, leftPorts j ≠ (4 : Fin 5) := by intro j; fin_cases j <;> decide
    simpa [store5] using StackProgPortLift.write_outside_local leftPorts
      (CookPvsNP.CanonicalBlockParser.store a b c) (store5 input left right status result) ho

private theorem write_right (a b c input left right status result : List BSym) :
    write rightPorts (CookPvsNP.CanonicalBlockParser.store a b c) (store5 input left right status result) =
      store5 a left b c result := by
  funext k
  fin_cases k
  · simpa [rightPorts, CookPvsNP.CanonicalBlockParser.store, store5] using
      (StackProgPortLift.write_at_local rightPorts (CookPvsNP.CanonicalBlockParser.store a b c)
        (store5 input left right status result) (0 : Fin 3))
  · have ho : ∀ j : Fin 3, rightPorts j ≠ (1 : Fin 5) := by intro j; fin_cases j <;> decide
    simpa [store5] using StackProgPortLift.write_outside_local rightPorts
      (CookPvsNP.CanonicalBlockParser.store a b c) (store5 input left right status result) ho
  · simpa [rightPorts, CookPvsNP.CanonicalBlockParser.store, store5] using
      (StackProgPortLift.write_at_local rightPorts (CookPvsNP.CanonicalBlockParser.store a b c)
        (store5 input left right status result) (1 : Fin 3))
  · simpa [rightPorts, CookPvsNP.CanonicalBlockParser.store, store5] using
      (StackProgPortLift.write_at_local rightPorts (CookPvsNP.CanonicalBlockParser.store a b c)
        (store5 input left right status result) (2 : Fin 3))
  · have ho : ∀ j : Fin 3, rightPorts j ≠ (4 : Fin 5) := by intro j; fin_cases j <;> decide
    simpa [store5] using StackProgPortLift.write_outside_local rightPorts
      (CookPvsNP.CanonicalBlockParser.store a b c) (store5 input left right status result) ho

private theorem write_compare (a b c input left right status result : List BSym) :
    write comparePorts (TwoAgentSched.TotalTotal.StackCompareDigits.store a b c) (store5 input left right status result) =
      store5 input a b status c := by
  funext k
  fin_cases k
  · have ho : ∀ j : Fin 3, comparePorts j ≠ (0 : Fin 5) := by intro j; fin_cases j <;> decide
    simpa [store5] using StackProgPortLift.write_outside_local comparePorts
      (TwoAgentSched.TotalTotal.StackCompareDigits.store a b c) (store5 input left right status result) ho
  · simpa [comparePorts, TwoAgentSched.TotalTotal.StackCompareDigits.store, store5] using
      (StackProgPortLift.write_at_local comparePorts (TwoAgentSched.TotalTotal.StackCompareDigits.store a b c)
        (store5 input left right status result) (0 : Fin 3))
  · simpa [comparePorts, TwoAgentSched.TotalTotal.StackCompareDigits.store, store5] using
      (StackProgPortLift.write_at_local comparePorts (TwoAgentSched.TotalTotal.StackCompareDigits.store a b c)
        (store5 input left right status result) (1 : Fin 3))
  · have ho : ∀ j : Fin 3, comparePorts j ≠ (3 : Fin 5) := by intro j; fin_cases j <;> decide
    simpa [store5] using StackProgPortLift.write_outside_local comparePorts
      (TwoAgentSched.TotalTotal.StackCompareDigits.store a b c) (store5 input left right status result) ho
  · simpa [comparePorts, TwoAgentSched.TotalTotal.StackCompareDigits.store, store5] using
      (StackProgPortLift.write_at_local comparePorts (TwoAgentSched.TotalTotal.StackCompareDigits.store a b c)
        (store5 input left right status result) (2 : Fin 3))

private theorem left_exec (input left right status result input' left' status' : List BSym)
    (steps : ℕ) (h : parseCanonicalBlockProg.Exec
      (CookPvsNP.CanonicalBlockParser.store input left status)
      (CookPvsNP.CanonicalBlockParser.store input' left' status') steps) :
    (liftProgC leftPorts leftInverse parseCanonicalBlockProg).Exec
      (store5 input left right status result) (store5 input' left' right status' result) steps := by
  have hp : project leftPorts (store5 input left right status result) =
      CookPvsNP.CanonicalBlockParser.store input left status := by
    funext k
    fin_cases k <;> simp [project, leftPorts, store5, CookPvsNP.CanonicalBlockParser.store]
  have hr := liftProgC_exec leftPorts leftInverse leftInverse_correct h
    (store5 input left right status result) hp
  rw [write_left] at hr
  exact hr

private theorem right_exec (input left right status result input' right' status' : List BSym)
    (steps : ℕ) (h : parseCanonicalBlockProg.Exec
      (CookPvsNP.CanonicalBlockParser.store input right status)
      (CookPvsNP.CanonicalBlockParser.store input' right' status') steps) :
    (liftProgC rightPorts rightInverse parseCanonicalBlockProg).Exec
      (store5 input left right status result) (store5 input' left right' status' result) steps := by
  have hp : project rightPorts (store5 input left right status result) =
      CookPvsNP.CanonicalBlockParser.store input right status := by
    funext k
    fin_cases k <;> simp [project, rightPorts, store5, CookPvsNP.CanonicalBlockParser.store]
  have hr := liftProgC_exec rightPorts rightInverse rightInverse_correct h
    (store5 input left right status result) hp
  rw [write_right] at hr
  exact hr

private theorem compare_exec (input left right status result left' right' result' : List BSym)
    (steps : ℕ) (h : compareFullProg.Exec
      (TwoAgentSched.TotalTotal.StackCompareDigits.store left right result)
      (TwoAgentSched.TotalTotal.StackCompareDigits.store left' right' result') steps) :
    (liftProgC comparePorts compareInverse compareFullProg).Exec
      (store5 input left right status result) (store5 input left' right' status result') steps := by
  have hp : project comparePorts (store5 input left right status result) =
      TwoAgentSched.TotalTotal.StackCompareDigits.store left right result := by
    funext k
    fin_cases k <;> simp [project, comparePorts, store5, TwoAgentSched.TotalTotal.StackCompareDigits.store]
  have hr := liftProgC_exec comparePorts compareInverse compareInverse_correct h
    (store5 input left right status result) hp
  rw [write_compare] at hr
  exact hr


/-- On two actual canonical number codes, the composed program halts in time
    linear in their bit lengths, preserves the suffix, and returns a less
    marker exactly when the first number is numerically smaller. -/
theorem parseCompare_exec (m n : ℕ) (tail : List BSym) :
    ∃ (steps : ℕ) (left right result : List BSym),
      steps ≤ 3 * m.bits.length + 3 * n.bits.length +
        3 * min m.bits.length n.bits.length + 21 ∧
      parseCompare.Exec (store5 (encNat m ++ (encNat n ++ tail)) [] [] [] [.sep])
        (store5 tail left right [.one, .one, .one, .one] result) steps ∧
      (result.head? = some .zero ↔ m < n) := by
  have hp1 := left_exec (encNat m ++ (encNat n ++ tail)) [] [] [] [.sep]
    (encNat n ++ tail) (m.bits.map CookPvsNP.CanonicalBlockParser.digitSym).reverse [.one, .one]
    (3 * m.bits.length + 7) (execution_and_bounds.1 m (encNat n ++ tail) [])
  have hp2 := right_exec (encNat n ++ tail) (m.bits.map CookPvsNP.CanonicalBlockParser.digitSym).reverse
    [] [.one, .one] [.sep] tail (n.bits.map CookPvsNP.CanonicalBlockParser.digitSym).reverse
    [.one, .one, .one, .one] (3 * n.bits.length + 7)
    (execution_and_bounds.1 n tail [.one, .one])
  obtain ⟨k, left, right, result, hk, hc, hresult⟩ := correct_and_total.1 m n
  have hdigit : CookPvsNP.CanonicalBlockParser.digitSym = TwoAgentSched.TotalTotal.StackCompareDigits.digitSym := rfl
  have hleft : (m.bits.map CookPvsNP.CanonicalBlockParser.digitSym).reverse =
      m.bits.reverse.map TwoAgentSched.TotalTotal.StackCompareDigits.digitSym := by simp [hdigit]
  have hright : (n.bits.map CookPvsNP.CanonicalBlockParser.digitSym).reverse =
      n.bits.reverse.map TwoAgentSched.TotalTotal.StackCompareDigits.digitSym := by simp [hdigit]
  rw [← hleft, ← hright] at hc
  have hcmp := compare_exec tail (m.bits.map CookPvsNP.CanonicalBlockParser.digitSym).reverse
    (n.bits.map CookPvsNP.CanonicalBlockParser.digitSym).reverse [.one, .one, .one, .one] [.sep]
    left right result k hc
  have hseq := StackProg.Exec.seq hp1 (StackProg.Exec.seq hp2 hcmp)
  refine ⟨(3 * m.bits.length + 7) + 1 + ((3 * n.bits.length + 7) + 1 + k),
    left, right, result, ?_, ?_, hresult⟩
  · omega
  · exact hseq

end TwoAgentSched.TotalTotal.ParseCompare

open TwoAgentSched.TotalTotal.ParseCompare
open TwoAgentSched.TotalTotal.StackCompareDigits

theorem solution :
    (∀ (m n : ℕ) (tail : List BSym),
      ∃ (steps : ℕ) (left right result : List BSym),
        steps ≤ 3 * m.bits.length + 3 * n.bits.length +
          3 * min m.bits.length n.bits.length + 21 ∧
        parseCompare.Exec (store5 (encNat m ++ (encNat n ++ tail)) [] [] [] [.sep])
          (store5 tail left right [.one, .one, .one, .one] result) steps ∧
        (result.head? = some .zero ↔ m < n)) ∧
    (∀ input : List BSym, ∃ (out : Fin 5 → List BSym) (steps : ℕ),
      parseCompare.Exec (store5 input [] [] [] [.sep]) out steps ∧
        steps ≤ 9 * input.length + 21) := by
  constructor
  · exact parseCompare_exec
  · intro input
    obtain ⟨rest1, digits1, status1, k1, hp1, hk1, hd1, hr1⟩ :=
      CookPvsNP.CanonicalBlockParser.execution_and_bounds.2 input []
    obtain ⟨rest2, digits2, status2, k2, hp2, hk2, hd2, hr2⟩ :=
      CookPvsNP.CanonicalBlockParser.execution_and_bounds.2 rest1 status1
    obtain ⟨out3, k3, hc, hk3⟩ := correct_and_total.2 digits1 digits2 [.sep]
    have hout : out3 = TwoAgentSched.TotalTotal.StackCompareDigits.store (out3 0) (out3 1) (out3 2) := by
      funext k
      fin_cases k <;> simp [TwoAgentSched.TotalTotal.StackCompareDigits.store]
    rw [hout] at hc
    have hl := TwoAgentSched.TotalTotal.ParseCompare.left_exec input [] [] [] [.sep] rest1 digits1 status1 k1 hp1
    have hr := TwoAgentSched.TotalTotal.ParseCompare.right_exec rest1 digits1 [] status1 [.sep] rest2 digits2 status2 k2 hp2
    have hcmp := TwoAgentSched.TotalTotal.ParseCompare.compare_exec rest2 digits1 digits2 status2 [.sep]
      (out3 0) (out3 1) (out3 2) k3 hc
    have hseq := StackProg.Exec.seq hl (StackProg.Exec.seq hr hcmp)
    refine ⟨_, k1 + 1 + (k2 + 1 + k3), hseq, ?_⟩
    have hmin := Nat.min_le_left digits1.length digits2.length
    omega
