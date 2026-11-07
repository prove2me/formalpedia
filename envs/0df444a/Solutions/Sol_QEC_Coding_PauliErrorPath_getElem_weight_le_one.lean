-- Prove2me | solution 1 for QEC.Coding.PauliErrorPath.getElem_weight_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:51:43.553694+00:00
-- url     : https://prove2.me/submissions/f6b91d25-bcac-4b6d-8ebc-cd790b6a6b27

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
theorem _root_.solution (γ : PauliErrorPath (ι := ι)) (n : Nat)
    (hn : n < γ.increments.length) :
    weight γ.increments[n] ≤ 1 :=
  γ.step_weight_le_one γ.increments[n] (List.getElem_mem hn)
end QEC.Coding.PauliErrorPath
