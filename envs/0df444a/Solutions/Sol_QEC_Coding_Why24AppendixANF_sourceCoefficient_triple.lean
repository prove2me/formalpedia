-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:38:44.91282+00:00
-- url     : https://prove2.me/submissions/22b7cc1e-30c9-4939-9d5d-1f6bffa99e91

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
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_first_0
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_first_1
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_first_2
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_first_3
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_first_4
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_first_5
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_first_6
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_first_7

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (first second third : Fin 10)
    (hfirst : first < second) (hsecond : second < third) :
    sourceTripleCoefficient first second third =
      cubicGateCoefficient first second third := by
  fin_cases first
  · exact sourceCoefficient_triple_first_0 second third hfirst hsecond
  · exact sourceCoefficient_triple_first_1 second third hfirst hsecond
  · exact sourceCoefficient_triple_first_2 second third hfirst hsecond
  · exact sourceCoefficient_triple_first_3 second third hfirst hsecond
  · exact sourceCoefficient_triple_first_4 second third hfirst hsecond
  · exact sourceCoefficient_triple_first_5 second third hfirst hsecond
  · exact sourceCoefficient_triple_first_6 second third hfirst hsecond
  · exact sourceCoefficient_triple_first_7 second third hfirst hsecond
  · change (8 : Nat) < second.val at hfirst
    change second.val < third.val at hsecond
    omega
  · change (9 : Nat) < second.val at hfirst
    change second.val < third.val at hsecond
    omega
end QEC.Coding.Why24AppendixANF
