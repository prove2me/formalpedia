-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_linProj_smul_firstCoordVec_862aecb3e19a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:02:31.586134+00:00
-- url     : https://prove2.me/submissions/ad2f13ea-f821-4c4f-bb19-bdb5318a029a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLeadBlockGaussTail

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
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LeadBlockGaussTail
namespace GroundTheory.Heights₂.Heights.LeadBlockGaussTail
theorem _root_.solution {m n : ℕ} (π : Fin m → Fin n → ℂ) (r : ℝ) (c0 : Fin n)
    (hc0 : (c0 : ℕ) = 0) (i : Fin m) :
    linProj π ((r : ℂ) • firstCoordVec n) i = (r : ℂ) * π i c0 := by
  simp only [linProj, firstCoordVec]
  simp
  rw [Finset.sum_eq_single c0]
  · simp [hc0, mul_comm]
  · intro j _ hj
    have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext (h.trans hc0.symm))
    simp [this]
  · simp
end GroundTheory.Heights₂.Heights.LeadBlockGaussTail
