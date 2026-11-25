-- Prove2me | solution 1 for PI.RhsWLim.W.ZetaZeros.zF_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:42:13.886126+00:00
-- url     : https://prove2.me/submissions/1edd9435-ca01-4daf-9a51-c548a63ef2c9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_herm_fix
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_herm_emb
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_secP_eq

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
    zF k r z z' (chartF k r z z' μsec q) = q.1 := by
  obtain ⟨hζ, hh, hh'⟩ := hq
  have hu' := HU.isUnit_of_uh hh'.1
  have hinv : (Matrix.of q.2.2 : Mat k r)⁻¹ *ᵥ z' = z' := by
    conv_lhs => rw [← hh'.2.2]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu', Matrix.one_mulVec]
  show herm (Hpk k r) ((Matrix.of q.2.1 * embWb k r (secP k r z z' μsec q.1) * (Matrix.of q.2.2)⁻¹) *ᵥ z') z = q.1
  rw [← Matrix.mulVec_mulVec, hinv, ← Matrix.mulVec_mulVec, herm_fix (Hpk k r) (Matrix.of q.2.1) hh.1 z hh.2.2,
    secP_eq hζ, herm_emb _ hD.z_mem hD.z'_mem]
  exact (hD.sec.2 q.1 hζ).2
end PI.RhsWLim.W.ZetaZeros
