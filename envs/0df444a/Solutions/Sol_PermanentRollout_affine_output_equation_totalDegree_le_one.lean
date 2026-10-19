-- Prove2me | solution 1 for PermanentRollout.affine_output_equation_totalDegree_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/85e8d3f1-d073-4924-a745-5c15769bc8db

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} (output : MvPolynomial ι ℂ) (η : ℂ)
    (houtput : output.totalDegree ≤ 1) :
    (output - MvPolynomial.C η).totalDegree ≤ 1 :=
  (MvPolynomial.totalDegree_sub_C_le output η).trans houtput
end PermanentRollout
