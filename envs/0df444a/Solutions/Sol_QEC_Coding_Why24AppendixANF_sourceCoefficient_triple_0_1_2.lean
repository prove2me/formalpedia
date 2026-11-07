-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_1_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:44:13.985995+00:00
-- url     : https://prove2.me/submissions/1182fdcd-5340-4750-8293-aad7128b175d

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Probe
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part00
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_1_2_probe


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution :
    sourceTripleCoefficient 0 1 2 = cubicGateCoefficient 0 1 2 := by
  exact sourceCoefficient_triple_0_1_2_probe
end QEC.Coding.Why24AppendixANF
