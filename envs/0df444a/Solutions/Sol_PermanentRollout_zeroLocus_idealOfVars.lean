-- Prove2me | solution 1 for PermanentRollout.zeroLocus_idealOfVars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/46fdb115-9fe5-4d59-bff0-03572afae1df

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
theorem _root_.solution {ι : Type*} :
    MvPolynomial.zeroLocus ℂ (MvPolynomial.idealOfVars ι ℂ) =
      ({0} : Set (ι → ℂ)) := by
  rw [MvPolynomial.idealOfVars, MvPolynomial.zeroLocus_span]
  ext point
  simp [MvPolynomial.aeval_def, funext_iff]
end PermanentRollout
