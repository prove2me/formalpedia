-- Prove2me | solution 1 for PascalMinusOnePalomar.minus_one_valuation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:27:29.849856+00:00
-- url     : https://prove2.me/submissions/9d58ef45-e243-460d-9646-462301ddf5f9

import Definitions.Def_PascalMinusOne
import Definitions.Def_PascalMinusOne_Solution
import Theorems.Thm_PascalMinusOne_evenDigitSum_zero
import Theorems.Thm_PascalMinusOne_mem_admissibleIndices_iff
import Theorems.Thm_PascalMinusOne_minus_one_valuation
import Theorems.Thm_PascalMinusOne_oddDigitSum_zero
import Theorems.Thm_PascalMinusOne_parityDigitSums_cons
import Theorems.Thm_PascalMinusOne_parityDigitSums_nil
import Theorems.Thm_PascalMinusOne_signedZeroSum_m_zero
import Theorems.Thm_PascalMinusOne_signedZeroSum_one_one
import Theorems.Thm_PascalMinusOne_signedZeroSum_zero_m
attribute [local simp] PascalMinusOne.evenDigitSum_zero
attribute [local simp] PascalMinusOne.mem_admissibleIndices_iff
attribute [local simp] PascalMinusOne.oddDigitSum_zero
attribute [local simp] PascalMinusOne.parityDigitSums_cons
attribute [local simp] PascalMinusOne.parityDigitSums_nil
attribute [local simp] PascalMinusOne.signedZeroSum_m_zero
attribute [local simp] PascalMinusOne.signedZeroSum_one_one
attribute [local simp] PascalMinusOne.signedZeroSum_zero_m


section
namespace PascalMinusOnePalomar
private theorem G_eq_project (N m : ℕ) :
    G N m = PascalMinusOne.G N m := by
  rfl
private theorem parityDigitSums_eq_project (L : List ℕ) :
    parityDigitSums L = PascalMinusOne.parityDigitSums L := by
  induction L with
  | nil => rfl
  | cons d ds ih =>
      simp [parityDigitSums, PascalMinusOne.parityDigitSums, ih]
private theorem evenDigitSum_eq_project (p N : ℕ) :
    evenDigitSum p N = PascalMinusOne.evenDigitSum p N := by
  simp [evenDigitSum, PascalMinusOne.evenDigitSum, parityDigitSums_eq_project]
private theorem oddDigitSum_eq_project (p N : ℕ) :
    oddDigitSum p N = PascalMinusOne.oddDigitSum p N := by
  simp [oddDigitSum, PascalMinusOne.oddDigitSum, parityDigitSums_eq_project]
private theorem minusOneExpectedValuation_eq_project (m p A B : ℕ) :
    minusOneExpectedValuation m p A B =
      PascalMinusOne.minusOneExpectedValuation m p A B := by
  rfl
end PascalMinusOnePalomar
end

set_option autoImplicit true
open PascalMinusOnePalomar
namespace PascalMinusOnePalomar
theorem _root_.solution
    {m N p : ℕ}
    (hm : 3 ≤ m) (hmN : m ∣ N) (hNm : m < N)
    (hp : p.Prime) (hpm : p % m = m - 1) :
    padicValNat p (G N m) =
      minusOneExpectedValuation m p (evenDigitSum p N) (oddDigitSum p N) := by
  simpa only [G_eq_project, evenDigitSum_eq_project, oddDigitSum_eq_project,
    minusOneExpectedValuation_eq_project] using
    (PascalMinusOne.minus_one_valuation
      (m := m) (N := N) (p := p) hm hmN hNm hp hpm)
end PascalMinusOnePalomar
