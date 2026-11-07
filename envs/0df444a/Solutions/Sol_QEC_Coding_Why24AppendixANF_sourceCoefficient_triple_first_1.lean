-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_first_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:33:13.076817+00:00
-- url     : https://prove2.me/submissions/50470da4-a13a-4d3c-99c9-4e2589e25e7f

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
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_2
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_3
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_4
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_5
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_6
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_7
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_8


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (second third : Fin 10)
    (hfirst : (1 : Fin 10) < second) (hsecond : second < third) :
    sourceTripleCoefficient 1 second third = cubicGateCoefficient 1 second third := by
  fin_cases second
  · change (1 : Nat) < 0 at hfirst
    omega
  · change (1 : Nat) < 1 at hfirst
    omega
  · exact sourceCoefficient_triple_1_2 third hsecond
  · exact sourceCoefficient_triple_1_3 third hsecond
  · exact sourceCoefficient_triple_1_4 third hsecond
  · exact sourceCoefficient_triple_1_5 third hsecond
  · exact sourceCoefficient_triple_1_6 third hsecond
  · exact sourceCoefficient_triple_1_7 third hsecond
  · exact sourceCoefficient_triple_1_8 third hsecond
  · change (9 : Nat) < third.val at hsecond
    omega
end QEC.Coding.Why24AppendixANF
