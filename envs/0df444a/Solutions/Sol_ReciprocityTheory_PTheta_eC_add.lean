-- Prove2me | solution 1 for ReciprocityTheory.PTheta.eC_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:56:04.592618+00:00
-- url     : https://prove2.me/submissions/d2863920-5538-47a9-a574-649006bc8181

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open ReciprocityTheory ReciprocityTheory.PTheta
namespace ReciprocityTheory.PTheta
theorem _root_.solution (x y : ℂ) : eC (x + y) = eC x * eC y := by
  simp only [eC, ← Complex.exp_add]
  congr 1
  ring
end ReciprocityTheory.PTheta
