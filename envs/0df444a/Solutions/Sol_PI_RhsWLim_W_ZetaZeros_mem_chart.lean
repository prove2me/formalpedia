-- Prove2me | solution 1 for PI.RhsWLim.W.ZetaZeros.mem_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:00:48.565517+00:00
-- url     : https://prove2.me/submissions/8e350337-08ec-4f9e-ad72-aa50baa23149

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_secP_eq
import Theorems.Thm_PI_RhsWLim_W_MB_emb_mem_UWb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
open PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
namespace PI.RhsWLim.W.ZetaZeros
theorem _root_.solution (hD : WbData k r z z' μW μW' a a' μsec) {q : ℂ × Mt k r × Mt k r} (hq : q ∈ goodS k r z z') :
    Matrix.of (chartF k r z z' μsec q) ∈ UWb k r := by
  obtain ⟨hζ, hh, hh'⟩ := hq
  have sub : ∀ {w : Fin (2 * r + k + 1) → ℂ} {g : Mat k r}, g ∈ UWset k r w → g ∈ UWb k r :=
    fun hg => ⟨hg.1, hg.2.1⟩
  show Matrix.of q.2.1 * embWb k r (secP k r z z' μsec q.1) * (Matrix.of q.2.2)⁻¹ ∈ UWb k r
  rw [secP_eq hζ]
  exact HU.uwb_mul (HU.uwb_mul (sub hh) (MB.emb_mem_UWb (hD.sec.2 q.1 hζ).1)) (HU.uwb_inv (sub hh'))
end PI.RhsWLim.W.ZetaZeros
