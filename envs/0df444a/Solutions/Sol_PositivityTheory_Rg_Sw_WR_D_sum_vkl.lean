-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.sum_vkl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:04:10.170941+00:00
-- url     : https://prove2.me/submissions/62588879-e900-4f2d-9e90-70d94d741a8e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivFA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvXI
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivF
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_sum_ite_pair

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
theorem _root_.solution (hA : AlgA) (k l : Fin n) (x : Fin m → Fin n → ℂ) :
    ∑ a, ∑ b, vkl k l a b * (qX ε x a b : ℂ) = evX (Qp ε k l) x := by
  have h := congrFun (congrFun ((hA m n ε).2.1 x) k) l
  have g : gramX ε x k l = evX (Qp ε k l) x := rfl
  rw [← g, ← h]
  simp only [vkl, add_mul, Finset.sum_add_distrib]
  rw [sum_ite_pair k l _ (fun a b => (qX ε x a b : ℂ)), sum_ite_pair l k _ (fun a b => (qX ε x a b : ℂ))]
  simp only [herm]
  push_cast
  ring
end PositivityTheory.Rg.Sw.WR.D
