-- Prove2me | solution 1 for PalomarZF207.tm_bops_part3
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T23:31:43.749867+00:00
-- url     : https://prove2.me/submissions/8d41c259-6d33-4360-81ed-7f966966f5eb

import Definitions.Def_palomar_zf207_tm_check

open PalomarZF207TMCheck

set_option maxRecDepth 8192 in
private theorem c8 : chkBOpsTo (pB 881301) bopsChunk8 (pB 6805) = true := rfl
set_option maxRecDepth 8192 in
private theorem c9 : chkBOpsTo (pB 6805) bopsChunk9 (pB 375445) = true := rfl
set_option maxRecDepth 8192 in
private theorem c10 : chkBOpsTo (pB 375445) bopsChunk10 (pB 90517) = true := rfl
set_option maxRecDepth 8192 in
private theorem c11 : chkBOpsTo (pB 90517) bopsChunk11 (pB 45461) = true := rfl

theorem solution :
    chkBOpsTo (pB 881301) bopsChunk8 (pB 6805) = true ∧
    chkBOpsTo (pB 6805) bopsChunk9 (pB 375445) = true ∧
    chkBOpsTo (pB 375445) bopsChunk10 (pB 90517) = true ∧
    chkBOpsTo (pB 90517) bopsChunk11 (pB 45461) = true :=
  ⟨c8, c9, c10, c11⟩
