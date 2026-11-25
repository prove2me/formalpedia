-- Prove2me | solution 1 for PI.RhsWLim.W.ZetaZeros.nu_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:51:08.501469+00:00
-- url     : https://prove2.me/submissions/60db3127-21c2-4170-b04b-9e385e57e7d5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_repr
import Theorems.Thm_PI_RhsWLim_W_HU_lmulM_cont


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
theorem _root_.solution (hInv : RhsWInv) (hD : WbData k r z z' μW μW' a a' μsec) (s : Mat k r) (hs : s ∈ UWb k r) :
    (nuR k r z z' μW μW' μsec).map (lmulM s) = nuR k r z z' μW μW' μsec := by
  have hl : Measurable (lmulM s : Mt k r → Mt k r) := (HU.lmulM_cont s).measurable
  ext A hA
  have e : ((lmulM s) ⁻¹' A).indicator (1 : Mt k r → ℝ≥0∞) = fun x => A.indicator 1 (lmulM s x) := by
    funext x
    rfl
  rw [Measure.map_apply hl hA, ← lintegral_indicator_one (hl hA), ← lintegral_indicator_one hA,
    ← repr hD _ (measurable_one.indicator (hl hA)), ← repr hD _ (measurable_one.indicator hA), e,
    hInv k r z z' μW μW' a a' μsec hD s hs _ (measurable_one.indicator hA)]
end PI.RhsWLim.W.ZetaZeros
