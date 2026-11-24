-- Prove2me | solution 1 for ValueAwareRR.diagonalScore_minimizer_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:09:48.314341+00:00
-- url     : https://prove2.me/submissions/3ae56e1f-8ddd-4174-8687-11ea288c88f8

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_diagonalScore_signReverse
import Theorems.Thm_ValueAwareRR_diagonalScore_margin_table

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    diagonalScore m o = diagonalScore m proxySelectedOrder ↔
      o = proxySelectedOrder ∨ o = signReverse proxySelectedOrder := by
  constructor
  · intro h
    simp only [proxySelectedOrder] at h ⊢
    rcases o with ⟨r, s⟩
    cases s
    · have hmargin := diagonalScore_margin_table m r
      simp only [proxySelectedOrder] at hmargin
      cases r <;>
        norm_num [diagonalMarginTable, signReverse] at hmargin h ⊢ <;>
        nlinarith [sq_nonneg (m - 2)]
    · have hsign : diagonalScore m (r, true) = diagonalScore m (r, false) := by
        simpa [signReverse] using diagonalScore_signReverse m (r, false)
      rw [hsign] at h
      have hmargin := diagonalScore_margin_table m r
      simp only [proxySelectedOrder] at hmargin
      cases r <;>
        norm_num [diagonalMarginTable, signReverse] at hmargin h ⊢ <;>
        nlinarith [sq_nonneg (m - 2)]
  · intro h
    rcases h with h | h
    · subst o
      rfl
    · subst o
      exact diagonalScore_signReverse m proxySelectedOrder
end ValueAwareRR
