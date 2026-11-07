-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.selectedCoordinates_symm_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:43:15.857251+00:00
-- url     : https://prove2.me/submissions/6febdae8-f13b-42ac-813f-44b3832aed54

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Evaluation

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (word : Word) :
    f1024SelectedCoordinates.symm word =
      ∑ selected : Fin 10,
        word selected • f1024SelectedSelfDualBasis selected := by
  rw [f1024SelectedCoordinates, Module.Basis.equivFun_symm_apply]
end QEC.Coding.Why24AppendixANF
