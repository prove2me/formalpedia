-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_first_7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:35:01.23609+00:00
-- url     : https://prove2.me/submissions/bab8e004-bcce-4ad0-be3b-96421a9c7ed7

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part00
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part01
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part02
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part03
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part04
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part05
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part06
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part07
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part08
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part09
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part10
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part11
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part12
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part13
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part14
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part15
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Certificate
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_7_8


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (second third : Fin 10)
    (hfirst : (7 : Fin 10) < second) (hsecond : second < third) :
    sourceTripleCoefficient 7 second third = cubicGateCoefficient 7 second third := by
  fin_cases second
  · change (7 : Nat) < 0 at hfirst
    omega
  · change (7 : Nat) < 1 at hfirst
    omega
  · change (7 : Nat) < 2 at hfirst
    omega
  · change (7 : Nat) < 3 at hfirst
    omega
  · change (7 : Nat) < 4 at hfirst
    omega
  · change (7 : Nat) < 5 at hfirst
    omega
  · change (7 : Nat) < 6 at hfirst
    omega
  · change (7 : Nat) < 7 at hfirst
    omega
  · exact sourceCoefficient_triple_7_8 third hsecond
  · change (9 : Nat) < third.val at hsecond
    omega
end QEC.Coding.Why24AppendixANF
