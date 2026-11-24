-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CK.analyticAt_H
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:39:54.024232+00:00
-- url     : https://prove2.me/submissions/003708b6-2252-46f1-8466-e225857bdf1d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_AnalyticAtDet
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_analyticAt_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw.LVs
namespace PositivityTheory.Rg.Sw.LVs.CK
theorem _root_.solution (N : ℕ) (t : ℤ) (T0 : Matrix (Fin N) (Fin N) ℂ) (h : (1 + T0).det ≠ 0) :
    AnalyticAt ℂ (H N t) T0 := by
  have hd : AnalyticAt ℂ (fun T : Matrix (Fin N) (Fin N) ℂ => (1 + T).det) T0 :=
    (analyticAt_det (1 + T0)).comp (analyticAt_const.add analyticAt_id)
  exact hd.zpow h
end PositivityTheory.Rg.Sw.LVs.CK
