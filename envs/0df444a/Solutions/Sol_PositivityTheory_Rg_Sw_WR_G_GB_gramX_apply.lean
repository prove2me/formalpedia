-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.GB.gramX_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:04:00.353806+00:00
-- url     : https://prove2.me/submissions/3726f9c6-f459-4ee0-82b5-c64277d5701c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBaseB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_HermTranspose
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GB_evX_Qb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
open PositivityTheory.Rg.Sw.WR.G.GB
namespace PositivityTheory.Rg.Sw.WR.G.GB
theorem _root_.solution (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) :
    gramX ε x i j = ∑ a, ((sgnR ε a : ℝ) : ℂ) * (star (x a i) * x a j) := by
  unfold gramX
  rw [Qp, evX, map_sub, ← evX, ← evX, evX_Qb, evX_Qb, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold sgnR
  cases h : ε a <;> simp
end PositivityTheory.Rg.Sw.WR.G.GB
