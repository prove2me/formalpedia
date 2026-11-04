-- Prove2me | solution 1 for ThreeSum.LightMomentDeterminant.eval_leading
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:34:53.416628+00:00
-- url     : https://prove2.me/submissions/e9b9e23c-c39f-4bc6-b7fe-405112575c64

import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_determinant

set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentDeterminant
open Light Matrix ThreeSum.LightFixedArithmetic
open scoped BigOperators
namespace ThreeSum.LightMomentDeterminant
theorem _root_.solution (d : ℕ) (x : ℕ → ℤ) :
    (leading d).eval x=Matrix.det (Matrix.of (fun (i j : Fin d) => x (i.val+j.val+1))) := by
  rw [leading,eval_determinant]
  rfl
end ThreeSum.LightMomentDeterminant
