-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:45:21.627463+00:00
-- url     : https://prove2.me/submissions/f1c4aa7e-6422-46df-9afd-5cdcbf4411a3

import Definitions.Def_QEC_Coding_Stabilizer_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Correctability

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
open scoped ComplexConjugate
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution {α : Type v} [Fintype α]
    (E : α → Binary ι) (amp : α → Complex) (a : α) :
    (binaryPauliKrausFamily E amp).operator a = amp a • toQubitOperator (E a) := by
  classical
  rfl
end QEC.Coding.PauliSymplectic
