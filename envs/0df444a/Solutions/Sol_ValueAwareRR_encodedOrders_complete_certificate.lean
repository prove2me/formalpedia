-- Prove2me | solution 1 for ValueAwareRR.encodedOrders_complete_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:12:20.754466+00:00
-- url     : https://prove2.me/submissions/ef978bc9-a8f8-4f03-a751-0a59d96b5773

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_encodedPermutation_injective
import Theorems.Thm_ValueAwareRR_signedOrder_card
import Theorems.Thm_ValueAwareRR_fourPermutation_card

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution :
    Function.Injective encodedPermutation ∧
      Fintype.card SignedOrder = Fintype.card (Equiv.Perm (Fin 4)) := by
  exact ⟨encodedPermutation_injective, signedOrder_card.trans fourPermutation_card.symm⟩
end ValueAwareRR
