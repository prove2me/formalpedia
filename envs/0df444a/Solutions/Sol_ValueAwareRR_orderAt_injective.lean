-- Prove2me | solution 1 for ValueAwareRR.orderAt_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:07:10.613408+00:00
-- url     : https://prove2.me/submissions/f3939260-8074-4102-acf8-6219e113703f

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_representativeOrder_injective
import Theorems.Thm_ValueAwareRR_negateLabel_injective
import Theorems.Thm_ValueAwareRR_representativeFirst_lt_two
import Theorems.Thm_ValueAwareRR_reversedRepresentativeFirst_ge_two

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution : Function.Injective orderAt := by
  rintro ⟨r, s⟩ ⟨r', s'⟩ h
  cases s <;> cases s'
  · have hr : r = r' := representativeOrder_injective (by simpa [orderAt] using h)
    subst r'
    rfl
  · have h0 := congrFun h (0 : Fin 4)
    have hl := representativeFirst_lt_two r
    have hr := reversedRepresentativeFirst_ge_two r'
    simp [orderAt] at h0
    omega
  · have h0 := congrFun h (0 : Fin 4)
    have hl := reversedRepresentativeFirst_ge_two r
    have hr := representativeFirst_lt_two r'
    simp [orderAt] at h0
    omega
  · have hrep : representativeOrder r = representativeOrder r' := by
      funext k
      apply negateLabel_injective
      simpa [orderAt] using congrFun h k
    have hr : r = r' := representativeOrder_injective hrep
    subst r'
    rfl
end ValueAwareRR
