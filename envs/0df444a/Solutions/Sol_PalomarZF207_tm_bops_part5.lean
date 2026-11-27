-- Prove2me | solution 1 for PalomarZF207.tm_bops_part5
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T23:32:13.247354+00:00
-- url     : https://prove2.me/submissions/ef88c346-958f-4a39-9467-e7f995fb366b

import Definitions.Def_palomar_zf207_tm_check

open PalomarZF207TMCheck

set_option maxRecDepth 8192 in
private theorem c16 : chkBOpsTo (pB 30101) bopsChunk16 (pB 2965) = true := rfl
set_option maxRecDepth 8192 in
private theorem c17 : chkBOpsTo (pB 2965) bopsChunk17 (pB 14229) = true := rfl
set_option maxRecDepth 8192 in
private theorem c18 : chkBOpsTo (pB 14229) bopsChunk18 (pB 12181) = true := rfl

theorem solution :
    chkBOpsTo (pB 30101) bopsChunk16 (pB 2965) = true ∧
    chkBOpsTo (pB 2965) bopsChunk17 (pB 14229) = true ∧
    chkBOpsTo (pB 14229) bopsChunk18 (pB 12181) = true :=
  ⟨c16, c17, c18⟩
