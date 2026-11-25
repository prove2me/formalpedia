-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.FP_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:50:15.399907+00:00
-- url     : https://prove2.me/submissions/fc0f3daa-f0b9-4038-97e0-9819065fbecf

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivFA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvXI
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivF
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_FP_eq_integral_Fi

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
theorem _root_.solution (a : ℂ) (P : PX m n) :
    FP ε c t (MvPolynomial.C a * P) = a • FP ε c t P := by
  funext y
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [FP_eq_integral_Fi, FP_eq_integral_Fi, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Fi, evX, map_mul, MvPolynomial.eval_C]; ring
end PositivityTheory.Rg.Sw.WR.D
