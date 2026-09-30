-- Prove2me | solution 1 for WorkbookCorrected.plus_82619
-- status  : ACCEPTED   (disprove)
-- author  : @Sneed
-- created : 2026-09-30T09:44:44.745262+00:00
-- url     : https://prove2.me/submissions/29f5fae6-a2d8-4beb-8844-bad1d626f989

import Mathlib.Tactic.NormNum

theorem solution : ¬ (2 + 12 + 30 + 56 + 90 + 132 + 182 + 240 + 306 + 380 + 462 + 552 + 650 + 756 + 870 + 992 + 1122 + 1260 + 1406 + 1560 + 1722 + 1892 + 2070 + 2256 + 2450 + 2652 + 2862 + 3080 + 3306 + 3540 + 3782 + 4032 + 4290 + 4556 + 4830 + 5112 + 5402 + 5700 + 6006 + 6320 + 6642 + 6972 + 7310 + 7656 + 8010 + 8372 + 8742 + 9120 + 9506 + 9900 = 24500) := by
  norm_num
