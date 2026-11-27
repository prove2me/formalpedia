-- Prove2me | solution 1 for PalomarZF207.tm_bops_part4
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T23:31:57.929091+00:00
-- url     : https://prove2.me/submissions/6cbdcad8-8ca9-4dda-b929-f50a0ea02614

import Definitions.Def_palomar_zf207_tm_check

open PalomarZF207TMCheck

set_option maxRecDepth 8192 in
private theorem c12 : chkBOpsTo (pB 45461) bopsChunk12 (pB 2453) = true := rfl
set_option maxRecDepth 8192 in
private theorem c13 : chkBOpsTo (pB 2453) bopsChunk13 (pB 88469) = true := rfl
set_option maxRecDepth 8192 in
private theorem c14 : chkBOpsTo (pB 88469) bopsChunk14 (pB 80277) = true := rfl
set_option maxRecDepth 8192 in
private theorem c15 : chkBOpsTo (pB 80277) bopsChunk15 (pB 30101) = true := rfl

theorem solution :
    chkBOpsTo (pB 45461) bopsChunk12 (pB 2453) = true ∧
    chkBOpsTo (pB 2453) bopsChunk13 (pB 88469) = true ∧
    chkBOpsTo (pB 88469) bopsChunk14 (pB 80277) = true ∧
    chkBOpsTo (pB 80277) bopsChunk15 (pB 30101) = true :=
  ⟨c12, c13, c14, c15⟩
