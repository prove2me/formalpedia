-- Prove2me | solution 1 for ThreeSumApsp.flag_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:58:52.249214+00:00
-- url     : https://prove2.me/submissions/86da3aab-0044-4984-8fe2-46933478229f

import Mathlib.Algebra.Order.Ring.Int
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag

set_option autoImplicit false
section
open ThreeSumApsp
namespace ThreeSumApsp
theorem _root_.solution {p q : Prop} (h : p ↔ q) : flag p = flag q := by
  rw [propext h]
end ThreeSumApsp
