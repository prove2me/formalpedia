-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_first_6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:34:51.369536+00:00
-- url     : https://prove2.me/submissions/eb311e8c-74c8-47a6-87b7-f69f7b8784d7

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
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_6_7
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_6_8


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (second third : Fin 10)
    (hfirst : (6 : Fin 10) < second) (hsecond : second < third) :
    sourceTripleCoefficient 6 second third = cubicGateCoefficient 6 second third := by
  fin_cases second
  · change (6 : Nat) < 0 at hfirst
    omega
  · change (6 : Nat) < 1 at hfirst
    omega
  · change (6 : Nat) < 2 at hfirst
    omega
  · change (6 : Nat) < 3 at hfirst
    omega
  · change (6 : Nat) < 4 at hfirst
    omega
  · change (6 : Nat) < 5 at hfirst
    omega
  · change (6 : Nat) < 6 at hfirst
    omega
  · exact sourceCoefficient_triple_6_7 third hsecond
  · exact sourceCoefficient_triple_6_8 third hsecond
  · change (9 : Nat) < third.val at hsecond
    omega
end QEC.Coding.Why24AppendixANF
