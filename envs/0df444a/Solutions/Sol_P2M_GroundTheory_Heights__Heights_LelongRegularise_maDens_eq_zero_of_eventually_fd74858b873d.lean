-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LelongRegularise_maDens_eq_zero_of_eventually_fd74858b873d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:38:34.850119+00:00
-- url     : https://prove2.me/submissions/7f639277-a1e2-4d1c-b072-1ede8c6ff363

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongRegularise_mdisc_eq_zero_of_eq_zero_2c04554c731c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.LelongRegularise
namespace GroundTheory.Heights₂.Heights.LelongRegularise
theorem _root_.solution {D : ℕ} (F : Fin (D + 1) → (Fin (D + 1) → ℂ) → ℝ)
    {y : Fin (D + 1) → ℂ} (h : F 0 =ᶠ[𝓝 y] fun _ => 0) : ReciprocityTheory.AnForm.maDens F y = 0 := by
  have h2 : fderiv ℝ (fderiv ℝ (F 0)) y = 0 := by
    rw [(h.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]
    simp
  have hH : ReciprocityTheory.AnForm.hessC (F 0) y = 0 := by
    ext i j
    simp [ReciprocityTheory.AnForm.hessC, h2]
  unfold ReciprocityTheory.AnForm.maDens
  rw [mdisc_eq_zero_of_eq_zero (fun k => ReciprocityTheory.AnForm.hessC (F k) y) hH]
  simp
end GroundTheory.Heights₂.Heights.LelongRegularise
