-- Prove2me | solution 1 for QEC.Coding.PauliErrorPath.append_increments
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:22:09.946899+00:00
-- url     : https://prove2.me/submissions/ebf32d94-815a-4ad5-bc42-a70e315ae7eb

import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_ErrorPath

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
    (γ.append δ).increments = γ.increments ++ δ.increments :=
  rfl
end QEC.Coding.PauliErrorPath
