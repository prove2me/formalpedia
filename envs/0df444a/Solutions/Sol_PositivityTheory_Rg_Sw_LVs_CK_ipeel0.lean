-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CK.ipeel0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:37.590183+00:00
-- url     : https://prove2.me/submissions/e3fc46b8-fd0a-43cd-b85a-649d1913b3c9

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_AnalyticAtDet
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetDFin
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_isymm

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
theorem _root_.solution (G : F → ℂ) (x : F) (hG : AnalyticAt ℂ G x) (n : ℕ) (u : Fin (n + 1) → F) :
    iteratedFDeriv ℂ (n + 1) G x u = iteratedFDeriv ℂ n (fun y => fderiv ℂ G y (u 0)) x (fun k => u k.succ) := by
  have hfd : ContDiffAt ℂ n (fderiv ℂ G) x := (hG.contDiffAt (n := ω)).fderiv_right le_top
  have happ := (ContinuousLinearMap.apply ℂ ℂ (u 0)).iteratedFDeriv_comp_left hfd (i := n) le_rfl
  have hfun : (fun y => fderiv ℂ G y (u 0)) = (ContinuousLinearMap.apply ℂ ℂ (u 0)) ∘ fderiv ℂ G := rfl
  rw [← isymm G x hG (n + 1) u (finRotate (n + 1)), iteratedFDeriv_succ_apply_right, hfun, happ]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.apply_apply, finRotate_last]
  congr 2
  funext k
  simp [Fin.init, finRotate_succ_apply, Fin.coeSucc_eq_succ]
end PositivityTheory.Rg.Sw.LVs.CK
