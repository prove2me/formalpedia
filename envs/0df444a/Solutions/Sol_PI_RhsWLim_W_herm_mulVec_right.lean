-- Prove2me | solution 1 for PI.RhsWLim.W.herm_mulVec_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:42:49.8643+00:00
-- url     : https://prove2.me/submissions/ac060a65-f3f6-4d43-81a3-de2b913131d0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolURatio
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstPair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution {p : Mat k r} (hp : p ∈ UH (Hpk k r)) (v u : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v (p *ᵥ u) = herm (Hpk k r) (p⁻¹ *ᵥ v) u := by
  have hu := HU.isUnit_of_uh hp
  have hp' : pᴴ * Hpk k r * p = Hpk k r := hp
  have key : pᴴ * Hpk k r = Hpk k r * p⁻¹ := by
    calc pᴴ * Hpk k r = pᴴ * Hpk k r * (p * p⁻¹) := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
      _ = (pᴴ * Hpk k r * p) * p⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Hpk k r * p⁻¹ := by rw [hp']
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec]
end PI.RhsWLim.W
