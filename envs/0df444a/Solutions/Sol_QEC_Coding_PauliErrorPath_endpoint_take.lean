-- Prove2me | solution 1 for QEC.Coding.PauliErrorPath.endpoint_take
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:22:08.91399+00:00
-- url     : https://prove2.me/submissions/6f1dc0ed-e98f-411d-a942-802d96eb718b

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
theorem _root_.solution (γ : PauliErrorPath (ι := ι)) (n : Nat) :
    (γ.take n).endpoint = γ.stateAt n :=
  rfl
end QEC.Coding.PauliErrorPath
