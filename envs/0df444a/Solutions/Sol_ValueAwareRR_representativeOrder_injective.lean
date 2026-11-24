-- Prove2me | solution 1 for ValueAwareRR.representativeOrder_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:04:17.760609+00:00
-- url     : https://prove2.me/submissions/14aecb8b-6f2e-4b3f-8da2-b61db367ccf3

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution : Function.Injective representativeOrder := by
  intro r r' h
  have h0 := congrFun h (0 : Fin 4)
  have h1 := congrFun h (1 : Fin 4)
  have h2 := congrFun h (2 : Fin 4)
  have h3 := congrFun h (3 : Fin 4)
  cases r <;> cases r' <;> simp_all [representativeOrder]
end ValueAwareRR
