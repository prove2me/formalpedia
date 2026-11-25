-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.Dkl_FP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:58:06.415643+00:00
-- url     : https://prove2.me/submissions/9f1508a3-7f03-4d15-b8d7-87891271102a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivFA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvXI
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivF
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_dirC_FP
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_sum_vkl

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
theorem _root_.solution (hI : IntG) (hA : AlgA) (hc : 0 < c) (P : PX m n) (k l : Fin n) :
    Dkl k l (FP ε c t P) = FP ε c t (MvPolynomial.C (Complex.I * t) * Qp ε k l * P) := by
  have hq := (hA m n ε).2.2.2.2
  funext y
  unfold Dkl
  rw [dirC_FP hI hq hc]
  unfold FP
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only
  rw [sum_vkl hA]
  simp only [Fi, evX, map_mul, MvPolynomial.eval_C]
  ring
end PositivityTheory.Rg.Sw.WR.D
