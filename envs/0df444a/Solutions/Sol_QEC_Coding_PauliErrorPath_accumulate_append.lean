-- Prove2me | solution 1 for QEC.Coding.PauliErrorPath.accumulate_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:31:15.76588+00:00
-- url     : https://prove2.me/submissions/e1f8f891-dd17-443c-be73-46f7beec6a36

import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_ErrorPath
import Theorems.Thm_QEC_Coding_PauliErrorPath_foldl_binaryMul_eq_binaryMul_accumulate

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
open QEC.Coding.PauliErrorPath
omit [DecidableEq ι]
namespace QEC.Coding.PauliErrorPath
theorem _root_.solution (left right : List (Binary ι)) :
    accumulate (left ++ right) =
      binaryMul (accumulate left) (accumulate right) := by
  rw [accumulate, List.foldl_append]
  exact foldl_binaryMul_eq_binaryMul_accumulate right (accumulate left)
end QEC.Coding.PauliErrorPath
