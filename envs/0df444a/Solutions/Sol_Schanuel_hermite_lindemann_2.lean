-- Prove2me | solution 2 for Schanuel.hermite_lindemann
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T12:44:15.474132+00:00
-- url     : https://prove2.me/submissions/365af89f-eeaa-4cb1-9845-0702b71014a1

import Mathlib
import Theorems.Thm_DiazModulus_hermite_lindemann_holds

-- `DiazModulus.hermite_lindemann_holds : HermiteLindemann`, Proved on this platform, is this
-- statement with the definition `HermiteLindemann` folded and the two hypotheses swapped.
theorem solution (a : ℂ) (ha : IsAlgebraic ℚ a) (ha0 : a ≠ 0) :
    Transcendental ℚ (Complex.exp a) :=
  DiazModulus.hermite_lindemann_holds a ha0 ha

#print axioms solution
