-- Prove2me | solution 1 for ValueAwareRR.negateLabel_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:04:35.075699+00:00
-- url     : https://prove2.me/submissions/c113a1d3-3d32-492e-9bd1-ea22fa22eff8

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution : Function.Injective negateLabel := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [negateLabel]
end ValueAwareRR
