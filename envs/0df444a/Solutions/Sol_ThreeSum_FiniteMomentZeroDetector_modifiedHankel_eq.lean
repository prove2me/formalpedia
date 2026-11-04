-- Prove2me | solution 1 for ThreeSum.FiniteMomentZeroDetector.modifiedHankel_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:43:26.647754+00:00
-- url     : https://prove2.me/submissions/181db278-77cf-4512-b2d2-b885409adcf3

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Theorems.Thm_ThreeSum_FiniteMomentZeroDetector_modifiedMoment_eq

set_option autoImplicit false
open ThreeSum ThreeSum.FiniteMomentZeroDetector
open Matrix Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
namespace ThreeSum.FiniteMomentZeroDetector
theorem _root_.solution {t : ℕ} (v w : Fin t → ℤ) (a : ℤ) (d : ℕ) :
    modifiedHankel v w a d=hankel v (fun s => w s*(v s-a)^2) d := by
  ext i j
  exact modifiedMoment_eq v w a (i.val+j.val)
end ThreeSum.FiniteMomentZeroDetector
