-- Prove2me | solution 1 for ThreeSum.LightPolynomialCoefficient.raw_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:14:38.177618+00:00
-- url     : https://prove2.me/submissions/b66aed8b-5ea2-41a8-924d-824278c5b8f4

import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_Submission_ThreeSum_LightPolynomialCoefficient

set_option autoImplicit false
open ThreeSum ThreeSum.LightPolynomialCoefficient
open Light Finset
set_option maxHeartbeats 2000000
namespace ThreeSum.LightPolynomialCoefficient
theorem _root_.solution (f g : ℕ → ℕ) (j m k : ℕ) :
    rawCoefficient f g (j+1) m k=rawCoefficient f g j m k+term f g m k j :=
  sum_range_succ _ _
end ThreeSum.LightPolynomialCoefficient
