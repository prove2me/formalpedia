-- Prove2me | solution 1 for ThreeSum.TernaryReconstruction.inverseDigit_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:04:07.035204+00:00
-- url     : https://prove2.me/submissions/2b187074-1c21-410e-be84-a7833a5ce703

import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryReconstruction
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryQuery ThreeSum.TernaryEuler
namespace ThreeSum.TernaryReconstruction
theorem _root_.solution (f : Fin 3 → ℤ) (q : Fin 3) :
    inverseDigit f q = ∑ r : Fin 3, inverseCoefficient q r * f r := by
  fin_cases q <;>
    norm_num [inverseDigit, inverseCoefficient, Fin.sum_univ_succ,
      Fin.le_def, Nat.choose, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide] <;> ring
end ThreeSum.TernaryReconstruction
