-- Prove2me | solution 1 for P2M_FixedOrderFactor_sqrtCount_le_of_dvd__c2eccb1785d4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:03:24.094622+00:00
-- url     : https://prove2.me/submissions/677859c3-ac6f-4d95-a912-55193fd8ea5b

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias

set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (M a : ℕ) {s s' : ℕ} (h : s' ∣ s) :
    sqrtCount M a s ≤ sqrtCount M a s' := by
  unfold sqrtCount
  apply card_le_card
  intro x hx
  simp only [mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.1, hx.2.2.1, h.trans hx.2.2.2⟩
end FixedOrderFactor
