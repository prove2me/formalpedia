-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMeanFubini_preimage_ballProd_fbe88fcf28b0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:16:55.440165+00:00
-- url     : https://prove2.me/submissions/bd733ed6-9127-404c-967b-accab787505d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSphereMeanFubini
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanFubini_consEquiv_apply_f1f52a18dac4

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
open MeasureTheory Measure Set
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMeanFubini
namespace GroundTheory.Heights₂.Heights.SphereMeanFubini
theorem _root_.solution {n : ℕ} (h : HermNorm n) (k : ℕ) :
    consEquiv k ⁻¹' ballProd h (k + 1) = ballH h ×ˢ ballProd h k := by
  ext p
  simp only [mem_preimage, consEquiv_apply, ballProd, mem_ofPred_eq, mem_prod, ballH,
    Fin.forall_fin_succ, consGroup, Fin.cases_zero, Fin.cases_succ]
end GroundTheory.Heights₂.Heights.SphereMeanFubini
