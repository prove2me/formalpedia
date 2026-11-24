-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CK.ipeel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:49.229167+00:00
-- url     : https://prove2.me/submissions/95f6ffef-4da9-4aca-88af-61149c0441dd

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_AnalyticAtDet
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetDFin
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_isymm
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_ipeel0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace PositivityTheory.Rg.Sw.LVs.CK
theorem _root_.solution (G : F → ℂ) (x : F) (hG : AnalyticAt ℂ G x) (n : ℕ) (u : Fin (n + 1) → F) (i0 : Fin (n + 1)) :
    iteratedFDeriv ℂ (n + 1) G x u = iteratedFDeriv ℂ n (fun y => fderiv ℂ G y (u i0)) x (fun k => u (i0.succAbove k)) := by
  rw [← isymm G x hG (n + 1) u i0.cycleRange.symm, ipeel0 G x hG n]
  simp [Fin.cycleRange_symm_zero, Fin.cycleRange_symm_succ]
end PositivityTheory.Rg.Sw.LVs.CK
