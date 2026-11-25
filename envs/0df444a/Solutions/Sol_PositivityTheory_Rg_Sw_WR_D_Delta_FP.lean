-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.Delta_FP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:24:57.398852+00:00
-- url     : https://prove2.me/submissions/7b4d041a-86d9-4729-871f-5b16ce88d0e5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivFA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvXI
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivF
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_FP_C_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_FP_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_foldr_FP
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_sum_perm_eq_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ}
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution (hI : IntG) (hA : AlgA) (hc : 0 < c) (P : PX m n) :
    Delta (FP ε c t P) = FP ε c t (MvPolynomial.C ((Complex.I * t) ^ n) * detQ ε * P) := by
  unfold Delta
  simp only [foldr_FP hI hA hc]
  rw [← sum_perm_eq_det (ε := ε) (t := t), Finset.sum_mul, FP_sum hI hA hc]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_assoc, FP_C_mul]
end PositivityTheory.Rg.Sw.WR.D
