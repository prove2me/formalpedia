-- Prove2me | solution 1 for Pr6453.word_receipts
-- status  : ACCEPTED   (prove)
-- author  : @gustasmickus
-- created : 2026-11-08T18:20:47.158574+00:00
-- url     : https://prove2.me/submissions/4d3849ed-c186-445b-b3c5-8d814c53040b

/-
PR #6453: the receipts of the word.
-/
import Definitions.Def_Pr6453_Word

set_option autoImplicit false

namespace Pr6453

theorem word_receipts :
    (census.map (fun p => p.2)).sum = 17926 ∧
      (helperHistogram.map (fun p => p.2)).sum = 562 ∧
      nativeReceipt.1 = 2941 ∧ physicalReceipt.1 = 799 := by
  refine ⟨by decide, by decide, rfl, rfl⟩

end Pr6453

/-- **The receipts of the PR #6453 word.** -/
theorem solution :
    (Pr6453.census.map (fun p => p.2)).sum = 17926 ∧
      (Pr6453.helperHistogram.map (fun p => p.2)).sum = 562 ∧
      Pr6453.nativeReceipt.1 = 2941 ∧ Pr6453.physicalReceipt.1 = 799 :=
  Pr6453.word_receipts
