-- Prove2me | solution 1 for QEC.Coding.why24QuditQubitUnitary_conjUOneSeven
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:09:59.380964+00:00
-- url     : https://prove2.me/submissions/7b184ce0-d65a-4aa6-826c-b1d4eb2ba8ee

import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution :
    why24QuditQubitUnitary.conjOperator why24UOneSeven = why24QubitUOneSeven := rfl
end QEC.Coding
