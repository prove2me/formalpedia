-- Prove2me | solution 1 for ThreeSum.TernaryReconstruction.frozenInverse_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:21.563744+00:00
-- url     : https://prove2.me/submissions/dfe05c87-5c78-4e5a-bc92-816078c89fe3

import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Theorems.Thm_ThreeSum_TernaryReconstruction_inverseDigit_eq_sum

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryReconstruction
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryQuery ThreeSum.TernaryEuler
namespace ThreeSum.TernaryReconstruction
theorem _root_.solution {N : ℕ} (i : Fin N) (rest : List (Fin N))
    (H : TritWord N → ℤ) (R : TritWord N) :
    frozenInverse (i :: rest) H R = ∑ d : Fin 3, inverseCoefficient (R i) d *
      frozenInverse rest H (Function.update R i d) :=
  inverseDigit_eq_sum _ _
end ThreeSum.TernaryReconstruction
