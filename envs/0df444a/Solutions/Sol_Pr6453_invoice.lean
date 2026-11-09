-- Prove2me | solution 1 for Pr6453.invoice
-- status  : ACCEPTED   (prove)
-- author  : @gustasmickus
-- created : 2026-11-08T16:16:30.000521+00:00
-- url     : https://prove2.me/submissions/2da4e8e4-2dac-457c-bfa2-eca5bf11c725

/-
PR #6453: the invoice function and the price inequality on it.
-/
import Definitions.Def_Pr6453_Invoice
import Definitions.Def_Pr6453_InvoiceEvents
import Theorems.Thm_Pr6453_moment_kappa_gt

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Pr6453

/-! ## The invoice of the PR #6453 word -/

/-- The invoice's target histogram is exactly the productive histogram that the price
inequality of `Pr6453.moment_kappa_gt` is stated for. -/
theorem invoice_targets_eq : toHist (invoiceTargets localHelpers) 200 = targets := by
  decide

/-- The invoice's paid histogram is exactly the paid histogram of the price inequality. -/
theorem invoice_paid_eq : toHist (invoicePaid localPaid) 200 = paid := by
  decide

/-- **The price inequality, stated for the invoice.** The moment inequality at the claimed
saving holds for the histograms the invoice produces from the local receipt, not merely for
two lists given in advance. -/
theorem invoice_moment_kappa_gt :
    moment (toHist (invoicePaid localPaid) 200) (1 - (kappa : ℝ)) <
      moment (toHist (invoiceTargets localHelpers) 200) (1 - (kappa : ℝ)) := by
  rw [invoice_targets_eq, invoice_paid_eq]
  exact moment_kappa_gt


/-!
## The event-level invoice

`pricing.py` computes the two histograms twice and checks that they agree: once by folding over
the word's events (`assemble`), once by the closed form (`formula_invoice`).  The fold uses only
the event tag and, for the idle events, the length of the idle list, so the word enters the
invoice through its census alone: 18 `LOCAL`, 17 `QUERY`, 14 `IDLE` of sizes `2,2,2,2,2,2,2,2,3,3,4,4,7,7`,
2 `IDLE_ONE` of size `2`, 20 `LAMBDA`, and 34 diagonal terms whose index sums are
`0, 2,…,2, 3,…, 4,…, 7,…, 9` (`physical.main_targets` of `RESULT.json`).

The block below formalises the fold and checks the agreement on that census.
-/

theorem toHist_eq_of_agree {f g : ℕ → ℕ} {N : ℕ} (h : ∀ r, r < N → f r = g r) :
    toHist f N = toHist g N := by
  have hm : (List.range N).map (fun r => (r, f r)) = (List.range N).map (fun r => (r, g r)) := by
    apply List.map_congr_left
    intro r hr
    rw [h r (List.mem_range.mp hr)]
  simp only [toHist]
  rw [hm]

/-- **The fold and the closed form agree** on the word's census, for every rank in the
support — the `need((targets, paid) == formula_invoice(local), ...)` check of `pricing.py`. -/
theorem assemble_agrees : ∀ r : Fin 200,
    (assemble wordEvents wordDiagonal localHelpers localPaid).1 r = invoiceTargets localHelpers r ∧
      (assemble wordEvents wordDiagonal localHelpers localPaid).2 r = invoicePaid localPaid r := by
  decide

/-- Hence the fold's target histogram is the priced one. -/
theorem assemble_targets_eq :
    toHist (assemble wordEvents wordDiagonal localHelpers localPaid).1 200 = targets := by
  rw [← invoice_targets_eq]
  apply toHist_eq_of_agree
  intro r hr
  exact (assemble_agrees ⟨r, hr⟩).1

/-- Hence the fold's paid histogram is the priced one. -/
theorem assemble_paid_eq :
    toHist (assemble wordEvents wordDiagonal localHelpers localPaid).2 200 = paid := by
  rw [← invoice_paid_eq]
  apply toHist_eq_of_agree
  intro r hr
  exact (assemble_agrees ⟨r, hr⟩).2

/-- **The price inequality, stated for the event fold**: for the word whose census this is, the
moments of the assembled histograms satisfy the inequality at the claimed saving. -/
theorem assemble_moment_kappa_gt :
    moment (toHist (assemble wordEvents wordDiagonal localHelpers localPaid).2 200)
        (1 - (kappa : ℝ)) <
      moment (toHist (assemble wordEvents wordDiagonal localHelpers localPaid).1 200)
        (1 - (kappa : ℝ)) := by
  rw [assemble_targets_eq, assemble_paid_eq]
  exact moment_kappa_gt

/-- The invoice, the event fold and the price inequality, together. -/
theorem invoice :
    toHist (invoiceTargets localHelpers) 200 = targets ∧
      toHist (invoicePaid localPaid) 200 = paid ∧
      toHist (assemble wordEvents wordDiagonal localHelpers localPaid).1 200 = targets ∧
      toHist (assemble wordEvents wordDiagonal localHelpers localPaid).2 200 = paid ∧
      moment (toHist (invoicePaid localPaid) 200) (1 - (kappa : ℝ)) <
        moment (toHist (invoiceTargets localHelpers) 200) (1 - (kappa : ℝ)) :=
  ⟨invoice_targets_eq, invoice_paid_eq, assemble_targets_eq, assemble_paid_eq,
    invoice_moment_kappa_gt⟩

end Pr6453

/-- **The invoice of the PR #6453 word.** -/
theorem solution :
    Pr6453.toHist (Pr6453.invoiceTargets Pr6453.localHelpers) 200 = Pr6453.targets ∧
      Pr6453.toHist (Pr6453.invoicePaid Pr6453.localPaid) 200 = Pr6453.paid ∧
      Pr6453.toHist (Pr6453.assemble Pr6453.wordEvents Pr6453.wordDiagonal
        Pr6453.localHelpers Pr6453.localPaid).1 200 = Pr6453.targets ∧
      Pr6453.toHist (Pr6453.assemble Pr6453.wordEvents Pr6453.wordDiagonal
        Pr6453.localHelpers Pr6453.localPaid).2 200 = Pr6453.paid ∧
      Pr6453.moment (Pr6453.toHist (Pr6453.invoicePaid Pr6453.localPaid) 200)
          (1 - (Pr6453.kappa : ℝ)) <
        Pr6453.moment (Pr6453.toHist (Pr6453.invoiceTargets Pr6453.localHelpers) 200)
          (1 - (Pr6453.kappa : ℝ)) :=
  Pr6453.invoice
