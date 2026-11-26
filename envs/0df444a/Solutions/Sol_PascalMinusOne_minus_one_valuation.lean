-- Prove2me | solution 1 for PascalMinusOne.minus_one_valuation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:25:27.371662+00:00
-- url     : https://prove2.me/submissions/613d6d7e-610b-4e51-8191-57f75c2465bf

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
import Theorems.Thm_PascalMinusOne_dvd_iff_signedZeroSum_digitSums
import Theorems.Thm_PascalMinusOne_parityDigitSums_add_eq_sum
import Theorems.Thm_PascalMinusOne_noBorrow_iff_proper_signed_zero_sum
import Theorems.Thm_PascalMinusOne_uniform_case_one_borrow_of_gt
import Theorems.Thm_PascalMinusOne_uniform_case_one_borrow_edge
import Theorems.Thm_PascalMinusOne_mixed_case_one_borrow_of_gt
import Theorems.Thm_PascalMinusOne_exceptional_mixed_no_one_borrow
import Theorems.Thm_PascalMinusOne_exceptional_mixed_two_borrow_witness
import Theorems.Thm_PascalMinusOne_evenDigitSum_zero
import Theorems.Thm_PascalMinusOne_mem_admissibleIndices_iff
import Theorems.Thm_PascalMinusOne_minimal_signed_zero_sum_classification
import Theorems.Thm_PascalMinusOne_oddDigitSum_zero
import Theorems.Thm_PascalMinusOne_padicVal_G_eq_of_lower_bound_of_witness
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



set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution
    {m N p : ℕ}
    (hm : 3 ≤ m) (hmN : m ∣ N) (hNm : m < N)
    (hp : p.Prime) (hpm : p % m = m - 1) :
    padicValNat p (G N m) =
      minusOneExpectedValuation m p (evenDigitSum p N) (oddDigitSum p N) := by
  have hm0 : 0 < m := by omega
  have hNne : N ≠ 0 := by omega
  have hdigitsNe : Nat.digits p N ≠ [] :=
    Nat.digits_ne_nil_iff_ne_zero.mpr hNne
  have hsumpos : 0 < (Nat.digits p N).sum :=
    List.sum_pos_iff_exists_pos_nat.mpr
      ⟨(Nat.digits p N).getLast hdigitsNe, List.getLast_mem hdigitsNe,
        Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero p hNne)⟩
  have hABpos :
      0 < evenDigitSum p N + oddDigitSum p N := by
    simpa [evenDigitSum, oddDigitSum, parityDigitSums_add_eq_sum] using hsumpos
  have hzero :
      SignedZeroSum m (evenDigitSum p N) (oddDigitSum p N) :=
    (dvd_iff_signedZeroSum_digitSums
      (m := m) (p := p) (k := N) (by omega) hpm).1 hmN
  have hpCase : p = m - 1 ∨ m < p := by
    by_cases hedge : p = m - 1
    · exact Or.inl hedge
    · right
      by_contra hnot
      have hple : p ≤ m := Nat.le_of_not_gt hnot
      by_cases hlt : p < m
      · have hpmod : p % m = p := Nat.mod_eq_of_lt hlt
        apply hedge
        omega
      · have hpeq : p = m := by omega
        subst p
        rw [Nat.mod_self] at hpm
        omega
  by_cases hproper :
      HasProperZeroSubmultiset m (evenDigitSum p N) (oddDigitSum p N)
  · have hwit0 :
        ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 0 :=
      (noBorrow_iff_proper_signed_zero_sum hm hp hpm hmN).2 hproper
    have hG0 : padicValNat p (G N m) = 0 :=
      padicVal_G_eq_of_lower_bound_of_witness
        hm0 hNm hp (fun _ _ ↦ Nat.zero_le _) hwit0
    have hnotminimal :
        ¬ MinimalSignedZeroSum m (evenDigitSum p N) (oddDigitSum p N) := by
      intro hminimal
      exact hminimal.2.2 hproper
    have hnotshapes :
        ¬ ((evenDigitSum p N = 1 ∧ oddDigitSum p N = 1) ∨
          (evenDigitSum p N = m ∧ oddDigitSum p N = 0) ∨
          (evenDigitSum p N = 0 ∧ oddDigitSum p N = m)) := by
      intro hshapes
      exact hnotminimal
        ((minimal_signed_zero_sum_classification hm).2 hshapes)
    have hnotMixed :
        ¬ (evenDigitSum p N = 1 ∧ oddDigitSum p N = 1) := by
      intro hmix
      exact hnotshapes (Or.inl hmix)
    have hnotUniform :
        ¬ ((evenDigitSum p N = m ∧ oddDigitSum p N = 0) ∨
          (evenDigitSum p N = 0 ∧ oddDigitSum p N = m)) := by
      intro hunif
      exact hnotshapes (Or.inr hunif)
    have hnotFirst :
        ¬ (evenDigitSum p N = 1 ∧ oddDigitSum p N = 1 ∧ p = m - 1) := by
      rintro ⟨heven, hodd, _⟩
      exact hnotMixed ⟨heven, hodd⟩
    have hnotSecond :
        ¬ (evenDigitSum p N = 1 ∧ oddDigitSum p N = 1 ∧ m < p) := by
      rintro ⟨heven, hodd, _⟩
      exact hnotMixed ⟨heven, hodd⟩
    simpa [minusOneExpectedValuation, hnotFirst, hnotSecond, hnotUniform] using hG0
  · have hminimal :
        MinimalSignedZeroSum m (evenDigitSum p N) (oddDigitSum p N) :=
      ⟨hABpos, hzero, hproper⟩
    have hpositive :
        ∀ k, Admissible N m k → 1 ≤ padicValNat p (N.choose k) := by
      intro k hkadm
      have hne : padicValNat p (N.choose k) ≠ 0 := by
        intro hval0
        apply hproper
        exact
          (noBorrow_iff_proper_signed_zero_sum hm hp hpm hmN).1
            ⟨k, hkadm, hval0⟩
      omega
    rcases (minimal_signed_zero_sum_classification hm).1 hminimal with
      hmixed | huniformLeft | huniformRight
    · rcases hmixed with ⟨heven, hodd⟩
      have hmixed' :
          evenDigitSum p N = 1 ∧ oddDigitSum p N = 1 :=
        ⟨heven, hodd⟩
      rcases hpCase with hedge | hgt
      · have hnoOne :
            ∀ k, Admissible N m k → padicValNat p (N.choose k) ≠ 1 :=
          exceptional_mixed_no_one_borrow hm hp hedge hmN hNm hmixed'
        have hlower2 :
            ∀ k, Admissible N m k → 2 ≤ padicValNat p (N.choose k) := by
          intro k hkadm
          have hpos := hpositive k hkadm
          have hne1 := hnoOne k hkadm
          omega
        have hwit2 :
            ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 2 :=
          exceptional_mixed_two_borrow_witness hm hp hedge hmN hNm hmixed'
        have hG2 : padicValNat p (G N m) = 2 :=
          padicVal_G_eq_of_lower_bound_of_witness
            hm0 hNm hp hlower2 hwit2
        have hexpected :
            minusOneExpectedValuation m p (evenDigitSum p N) (oddDigitSum p N) = 2 := by
          rw [minusOneExpectedValuation, if_pos ⟨heven, hodd, hedge⟩]
        exact hG2.trans hexpected.symm
      · have hwit1 :
            ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 1 :=
          mixed_case_one_borrow_of_gt hm hp hpm hgt hmixed'
        have hG1 : padicValNat p (G N m) = 1 :=
          padicVal_G_eq_of_lower_bound_of_witness
            hm0 hNm hp hpositive hwit1
        have hneEdge : p ≠ m - 1 := by omega
        simpa [minusOneExpectedValuation, heven, hodd, hgt, hneEdge] using hG1
    · rcases huniformLeft with ⟨heven, hodd⟩
      have huniform :
          (evenDigitSum p N = m ∧ oddDigitSum p N = 0) ∨
          (evenDigitSum p N = 0 ∧ oddDigitSum p N = m) :=
        Or.inl ⟨heven, hodd⟩
      have hwit1 :
          ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 1 := by
        rcases hpCase with hedge | hgt
        · rcases uniform_case_one_borrow_edge hm hp hedge hmN hNm huniform with
            ⟨t, s, k, hst, htocc, hsocc, hkdef, hkadm, hval⟩
          exact ⟨k, hkadm, hval⟩
        · exact uniform_case_one_borrow_of_gt hm hp hpm hgt hmN hNm huniform
      have hG1 : padicValNat p (G N m) = 1 :=
        padicVal_G_eq_of_lower_bound_of_witness
          hm0 hNm hp hpositive hwit1
      simpa [minusOneExpectedValuation, heven, hodd] using hG1
    · rcases huniformRight with ⟨heven, hodd⟩
      have huniform :
          (evenDigitSum p N = m ∧ oddDigitSum p N = 0) ∨
          (evenDigitSum p N = 0 ∧ oddDigitSum p N = m) :=
        Or.inr ⟨heven, hodd⟩
      have hwit1 :
          ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 1 := by
        rcases hpCase with hedge | hgt
        · rcases uniform_case_one_borrow_edge hm hp hedge hmN hNm huniform with
            ⟨t, s, k, hst, htocc, hsocc, hkdef, hkadm, hval⟩
          exact ⟨k, hkadm, hval⟩
        · exact uniform_case_one_borrow_of_gt hm hp hpm hgt hmN hNm huniform
      have hG1 : padicValNat p (G N m) = 1 :=
        padicVal_G_eq_of_lower_bound_of_witness
          hm0 hNm hp hpositive hwit1
      simpa [minusOneExpectedValuation, heven, hodd] using hG1
end PascalMinusOne
