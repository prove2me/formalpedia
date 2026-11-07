-- Prove2me | solution 1 for QEC.Coding.PauliErrorPath.endpoint_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:55:13.352202+00:00
-- url     : https://prove2.me/submissions/74bfc867-cd79-4be4-8b38-4cedaad15577

import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_ErrorPath
import Theorems.Thm_QEC_Coding_PauliErrorPath_accumulate_append

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
open QEC.Coding.PauliErrorPath
namespace QEC.Coding.PauliErrorPath
theorem _root_.solution (γ δ : PauliErrorPath (ι := ι)) :
    (γ.append δ).endpoint = binaryMul γ.endpoint δ.endpoint :=
  accumulate_append γ.increments δ.increments
end QEC.Coding.PauliErrorPath
