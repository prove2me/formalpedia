-- Prove2me | solution 1 for PermanentRollout.criticalLocus_eq_zeroLocus_pderiv_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/3a6adc58-acbf-49dc-be0d-5f91227a64aa

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {ι : Type} (P : MvPolynomial ι ℂ) :
    criticalLocus P =
      MvPolynomial.zeroLocus ℂ
        (Ideal.span (Set.range fun i : ι => MvPolynomial.pderiv i P)) := by
  rw [MvPolynomial.zeroLocus_span]
  ext point
  simp [criticalLocus, MvPolynomial.aeval_def]
end PermanentRollout
