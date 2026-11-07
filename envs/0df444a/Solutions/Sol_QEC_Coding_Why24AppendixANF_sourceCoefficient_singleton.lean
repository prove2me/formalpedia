-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:10:02.188986+00:00
-- url     : https://prove2.me/submissions/bf634938-16e1-40de-a709-771664b31f61

import Definitions.Def_QEC_Coding_QuditQubitConversion_BooleanANF
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Certificate
section
noncomputable section
namespace QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF
private theorem sourceCoefficient_singleton_0 : sourceCoefficient {0} = 1 := by decide
private theorem sourceCoefficient_singleton_1 : sourceCoefficient {1} = 1 := by decide
set_option maxRecDepth 2048 in
private theorem sourceCoefficient_singleton_2 : sourceCoefficient {2} = 1 := by decide
set_option maxRecDepth 2048 in
private theorem sourceCoefficient_singleton_3 : sourceCoefficient {3} = 1 := by decide
set_option maxRecDepth 2048 in
private theorem sourceCoefficient_singleton_4 : sourceCoefficient {4} = 1 := by decide
set_option maxRecDepth 2048 in
private theorem sourceCoefficient_singleton_5 : sourceCoefficient {5} = 1 := by decide
set_option maxRecDepth 2048 in
private theorem sourceCoefficient_singleton_6 : sourceCoefficient {6} = 1 := by decide
set_option maxRecDepth 2048 in
private theorem sourceCoefficient_singleton_7 : sourceCoefficient {7} = 1 := by decide
set_option maxRecDepth 2048 in
private theorem sourceCoefficient_singleton_8 : sourceCoefficient {8} = 1 := by decide
set_option maxRecDepth 2048 in
private theorem sourceCoefficient_singleton_9 : sourceCoefficient {9} = 1 := by decide
end QEC.Coding.Why24AppendixANF
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (coordinate : Fin 10) :
    sourceCoefficient {coordinate} = 1 := by
  fin_cases coordinate
  · exact sourceCoefficient_singleton_0
  · exact sourceCoefficient_singleton_1
  · exact sourceCoefficient_singleton_2
  · exact sourceCoefficient_singleton_3
  · exact sourceCoefficient_singleton_4
  · exact sourceCoefficient_singleton_5
  · exact sourceCoefficient_singleton_6
  · exact sourceCoefficient_singleton_7
  · exact sourceCoefficient_singleton_8
  · exact sourceCoefficient_singleton_9
end QEC.Coding.Why24AppendixANF
