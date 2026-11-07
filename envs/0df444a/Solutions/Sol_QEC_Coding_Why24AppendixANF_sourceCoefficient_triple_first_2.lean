-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_first_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:36:45.844218+00:00
-- url     : https://prove2.me/submissions/6370eab9-89dc-4f2c-890c-0b31560369b1

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
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_3
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_4
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_5
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_6
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_7
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_8


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (second third : Fin 10)
    (hfirst : (2 : Fin 10) < second) (hsecond : second < third) :
    sourceTripleCoefficient 2 second third = cubicGateCoefficient 2 second third := by
  fin_cases second
  · change (2 : Nat) < 0 at hfirst
    omega
  · change (2 : Nat) < 1 at hfirst
    omega
  · change (2 : Nat) < 2 at hfirst
    omega
  · exact sourceCoefficient_triple_2_3 third hsecond
  · exact sourceCoefficient_triple_2_4 third hsecond
  · exact sourceCoefficient_triple_2_5 third hsecond
  · exact sourceCoefficient_triple_2_6 third hsecond
  · exact sourceCoefficient_triple_2_7 third hsecond
  · exact sourceCoefficient_triple_2_8 third hsecond
  · change (9 : Nat) < third.val at hsecond
    omega
end QEC.Coding.Why24AppendixANF
