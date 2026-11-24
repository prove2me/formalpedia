-- Prove2me | solution 1 for ValueAwareRR.maxPrefixScore_minimizer_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:09:28.073007+00:00
-- url     : https://prove2.me/submissions/86599828-06c5-4198-9e20-ccf54473b29c

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_maxPrefixScore_signReverse
import Theorems.Thm_ValueAwareRR_maxPrefixScore_table

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    maxPrefixScore m o = maxPrefixScore m proxySelectedOrder ↔
      o = proxySelectedOrder ∨ o = signReverse proxySelectedOrder := by
  constructor
  · intro h
    simp only [proxySelectedOrder] at h ⊢
    rcases o with ⟨r, s⟩
    cases s
    · rw [maxPrefixScore_table m hm r,
        maxPrefixScore_table m hm .BDAC] at h
      cases r <;>
        simp [maxPrefixTable, signReverse] at h ⊢ <;> linarith
    · have hsign : maxPrefixScore m (r, true) = maxPrefixScore m (r, false) := by
        simpa [signReverse] using maxPrefixScore_signReverse m (r, false)
      rw [hsign, maxPrefixScore_table m hm r,
        maxPrefixScore_table m hm .BDAC] at h
      cases r <;>
        simp [maxPrefixTable, signReverse] at h ⊢ <;> linarith
  · intro h
    rcases h with h | h
    · subst o
      rfl
    · subst o
      exact maxPrefixScore_signReverse m proxySelectedOrder
end ValueAwareRR
