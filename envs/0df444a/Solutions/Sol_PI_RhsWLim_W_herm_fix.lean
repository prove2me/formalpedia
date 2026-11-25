-- Prove2me | solution 1 for PI.RhsWLim.W.herm_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:15:31.918949+00:00
-- url     : https://prove2.me/submissions/b707201d-de33-472d-a136-95822af57de3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest

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
theorem _root_.solution {h : Mat k r} {z : Fin (2 * r + k + 1) → ℂ} (hh : h ∈ UWset k r z) (u : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (h *ᵥ u) z = herm (Hpk k r) u z := by
  obtain ⟨hU, -, hfix⟩ := hh
  have hU' : hᴴ * PI.RhsWLim.Hpk k r * h = PI.RhsWLim.Hpk k r := hU
  unfold PI.RhsWLim.herm
  calc star z ⬝ᵥ (PI.RhsWLim.Hpk k r *ᵥ (h *ᵥ u))
      = star (h *ᵥ z) ⬝ᵥ (PI.RhsWLim.Hpk k r *ᵥ (h *ᵥ u)) := by rw [hfix]
    _ = star z ⬝ᵥ ((hᴴ * PI.RhsWLim.Hpk k r * h) *ᵥ u) := by
        rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = star z ⬝ᵥ (PI.RhsWLim.Hpk k r *ᵥ u) := by rw [hU']
end PI.RhsWLim.W
