-- Prove2me | solution 1 for PI.RhsWLim.W.RI.section_vector_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:03:48.034029+00:00
-- url     : https://prove2.me/submissions/f8b6c18c-3c50-4e06-b1c6-67ffcf680114

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvOA
import Theorems.Thm_PI_RhsWLim_W_MB_emb_mem_UWb
import Theorems.Thm_PI_RhsWLim_W_RI_herm_both
import Theorems.Thm_PI_RhsWLim_W_RI_inWb_emb
import Theorems.Thm_PI_RhsWLim_W_ZetaZeros_herm_emb


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
open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI
open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
namespace PI.RhsWLim.W.RI
theorem _root_.solution (hd : WbData k r z z' μW μW' a a' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    inWb k r (embWb k r (μsec ζ) *ᵥ z') ∧
      herm (Hpk k r) (embWb k r (μsec ζ) *ᵥ z') (embWb k r (μsec ζ) *ᵥ z') = herm (Hpk k r) z' z' ∧
      herm (Hpk k r) (embWb k r (μsec ζ) *ᵥ z') z = ζ := by
  refine ⟨inWb_emb _ hd.z'_mem, herm_both _ _ (MB.emb_mem_UWb (hd.sec.2 ζ hζ).1).1 z' z', ?_⟩
  rw [herm_emb _ hd.z_mem hd.z'_mem]
  exact (hd.sec.2 ζ hζ).2
end PI.RhsWLim.W.RI
