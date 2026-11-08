-- Prove2me | solution 1 for QEC.Coding.why24AppendixRetainedSites_eq_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:43:58.183083+00:00
-- url     : https://prove2.me/submissions/2700cec9-22e3-4592-90b6-d98017744ca0

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ReversePhase

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution :
    why24AppendixRetainedSites = ({0, 1, 2} : Finset (Fin 10)) :=
  rfl
end QEC.Coding
