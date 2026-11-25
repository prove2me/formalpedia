-- Prove2me | solution 1 for PI.RhsWLim.W.RI.inner_r
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:24:52.735839+00:00
-- url     : https://prove2.me/submissions/d2be1397-eb41-4642-8d50-e4eac88594f3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR
import Theorems.Thm_PI_RhsWLim_W_RI_uwset_inv

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
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI
open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
namespace PI.RhsWLim.W.RI
theorem _root_.solution (hW : IsHaarOn (UWset k r z') μW') (M : Mat k r) (φ : Mt k r → ℝ≥0∞) (hφ : Measurable φ)
    (b : Mat k r) (hb : b ∈ UWset k r z') :
    ∫⁻ h', φ (fun i j => (M * (Matrix.of h')⁻¹ * b) i j) ∂μW' =
      ∫⁻ h', φ (fun i j => (M * (Matrix.of h')⁻¹) i j) ∂μW' := by
  have hbi : b⁻¹ ∈ UWset k r z' := uwset_inv hb
  have hu : IsUnit (b⁻¹).det := HU.isUnit_of_uh hbi.1
  have hbu : IsUnit b.det := HU.isUnit_of_uh hb.1
  have hmap : μW'.map (lmulM b⁻¹) = μW' := hW.2.2.2 _ hbi
  have key : ∀ h' : Mt k r, M * (Matrix.of h')⁻¹ * b = M * (Matrix.of (lmulE b⁻¹ hu h'))⁻¹ := by
    intro h'
    change M * (Matrix.of h')⁻¹ * b = M * (b⁻¹ * Matrix.of h')⁻¹
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv b hbu, mul_assoc]
  calc ∫⁻ h', φ (fun i j => (M * (Matrix.of h')⁻¹ * b) i j) ∂μW'
      = ∫⁻ h', (fun y : Mt k r => φ (fun i j => (M * (Matrix.of y)⁻¹) i j)) (lmulE b⁻¹ hu h') ∂μW' := by
        refine lintegral_congr fun h' => ?_
        simp only [key h']
    _ = ∫⁻ y, φ (fun i j => (M * (Matrix.of y)⁻¹) i j) ∂(μW'.map (lmulE b⁻¹ hu)) :=
        by rw [lintegral_map_equiv]
    _ = ∫⁻ h', φ (fun i j => (M * (Matrix.of h')⁻¹) i j) ∂μW' := by
        rw [show ⇑(lmulE b⁻¹ hu) = lmulM b⁻¹ from rfl, hmap]
end PI.RhsWLim.W.RI
