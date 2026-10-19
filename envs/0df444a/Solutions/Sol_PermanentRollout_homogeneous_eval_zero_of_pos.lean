-- Prove2me | solution 1 for PermanentRollout.homogeneous_eval_zero_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/8615aa51-e998-463f-8a69-10c5ba39bd71

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
theorem _root_.solution {ι : Type*} {f : MvPolynomial ι ℂ}
    {e : ℕ} (he : 0 < e) (hf : f.IsHomogeneous e) :
    MvPolynomial.eval (0 : ι → ℂ) f = 0 := by
  rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
  exact hf.coeff_eq_zero (by simpa using he.ne)
end PermanentRollout
