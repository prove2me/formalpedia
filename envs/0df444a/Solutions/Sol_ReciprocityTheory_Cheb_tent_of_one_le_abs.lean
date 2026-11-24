-- Prove2me | solution 1 for ReciprocityTheory.Cheb.tent_of_one_le_abs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:56.437464+00:00
-- url     : https://prove2.me/submissions/09762180-58e0-4cb4-8b03-c28f8ad67a31

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsProdSubProdLeSumAbsSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution {t : ℝ} (h : 1 ≤ |t|) : tent t = 0 :=
  max_eq_left (by linarith)
end ReciprocityTheory.Cheb
