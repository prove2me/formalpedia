-- Prove2me | solution 1 for QEC.Coding.PauliErrorPath.states_getLast_eq_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:20:58.772789+00:00
-- url     : https://prove2.me/submissions/8fb54c9c-202e-4739-957f-a1dd335ac587

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
theorem _root_.solution (γ : PauliErrorPath (ι := ι)) :
    γ.states.getLast? = some γ.endpoint := by
  exact List.getLast?_scanl
end QEC.Coding.PauliErrorPath
