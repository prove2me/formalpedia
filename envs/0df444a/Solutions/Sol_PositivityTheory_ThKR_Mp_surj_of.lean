-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.surj_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:49:30.383012+00:00
-- url     : https://prove2.me/submissions/4a069e93-0aea-4ef9-9ff6-66adf525018b

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MapOfRealMul
import Theorems.Thm_PositivityTheory_ThKR_Mp_C_lo_mem
import Theorems.Thm_PositivityTheory_ThKR_Mp_C_lo_mul
import Theorems.Thm_P2M_PositivityTheory_ThKR_Mp_C_toBlocks___mul_lo_68e53e420ba7
import Theorems.Thm_PositivityTheory_ThKR_Mp_C_exists_det_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL
open scoped Real
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open C
namespace PositivityTheory.ThKR.Mp
theorem _root_.solution (h1 : DdNe l) (h2 : SecEx l) : Surj l := by
  intro s
  obtain ⟨t, ht⟩ := exists_det_ne s.1 (h1 s)
  let n : Sp l := ⟨lo t, lo_mem t⟩
  let m : Sp l := ⟨lo (-t), lo_mem (-t)⟩
  have e1 : (s * n).1.toBlocks₁₁.det ≠ 0 := by
    show (s.1 * lo t).toBlocks₁₁.det ≠ 0
    rw [toBlocks₁₁_mul_lo]
    exact ht
  have e2 : m.1.toBlocks₁₁.det ≠ 0 := by
    show (lo (l := l) (-t)).toBlocks₁₁.det ≠ 0
    simp [lo]
  obtain ⟨g1, -, hg1, -⟩ := h2 (s * n) e1
  obtain ⟨g2, -, hg2, -⟩ := h2 m e2
  refine ⟨g1 * g2, ?_⟩
  have hnm : n * m = 1 := Subtype.ext (lo_mul t)
  rw [map_mul, hg1, hg2, mul_assoc, hnm, mul_one]
end PositivityTheory.ThKR.Mp
