-- Prove2me | solution 1 for PalomarZF207.tm_bops_part2
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T23:31:27.232904+00:00
-- url     : https://prove2.me/submissions/d8fb625c-afbf-49cb-942a-fe2fd34f11b7

import Definitions.Def_palomar_zf207_tm_check

open PalomarZF207TMCheck

set_option maxRecDepth 8192 in
private theorem c4 : chkBOpsTo (pB 192721557) bopsChunk4 (pB 701077) = true := rfl
set_option maxRecDepth 8192 in
private theorem c5 : chkBOpsTo (pB 701077) bopsChunk5 (pB 6926997) = true := rfl
set_option maxRecDepth 8192 in
private theorem c6 : chkBOpsTo (pB 6926997) bopsChunk6 (pB 3912341) = true := rfl
set_option maxRecDepth 8192 in
private theorem c7 : chkBOpsTo (pB 3912341) bopsChunk7 (pB 881301) = true := rfl

theorem solution :
    chkBOpsTo (pB 192721557) bopsChunk4 (pB 701077) = true ∧
    chkBOpsTo (pB 701077) bopsChunk5 (pB 6926997) = true ∧
    chkBOpsTo (pB 6926997) bopsChunk6 (pB 3912341) = true ∧
    chkBOpsTo (pB 3912341) bopsChunk7 (pB 881301) = true :=
  ⟨c4, c5, c6, c7⟩
