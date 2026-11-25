-- Prove2me | solution 1 for PI.RhsWLim.W.RI.Gf_fib
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:13:51.761316+00:00
-- url     : https://prove2.me/submissions/585f5353-b553-414b-be3c-fd9b475c97dc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvO
import Theorems.Thm_PI_RhsWLim_W_RI_cont_act
import Theorems.Thm_PI_RhsWLim_W_RI_rmulM_cont


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
theorem _root_.solution (hU : UnimodK) (hT : FibTrans) (hW : IsHaarOn (UWset k r z) μW) (hfin : μW Set.univ ≠ ⊤)
    (hz : inWb k r z) (hTz : 0 < Tz k r z) {F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F)
    {v v' : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (hv' : inWb k r v')
    (h1 : herm (Hpk k r) v v = herm (Hpk k r) v' v') (h2 : herm (Hpk k r) v z = herm (Hpk k r) v' z) :
    Gf μW F v = Gf μW F v' := by
  obtain ⟨u, hu, huv⟩ := hT k r z v' v hz hv' hv hTz h1.symm h2.symm
  have hm : Measurable (fun y : Mt k r => F (Matrix.of y *ᵥ v')) :=
    hF.comp ((cont_act (k := k) (r := r)).comp (Continuous.prodMk continuous_const continuous_id)).measurable
  unfold Gf
  calc ∫⁻ h, F (Matrix.of h *ᵥ v) ∂μW = ∫⁻ h, (fun y : Mt k r => F (Matrix.of y *ᵥ v')) (rmulM u h) ∂μW := by
        refine lintegral_congr fun h => ?_
        show F (Matrix.of h *ᵥ v) = F ((Matrix.of h * u) *ᵥ v')
        rw [← Matrix.mulVec_mulVec, huv]
    _ = ∫⁻ y, F (Matrix.of y *ᵥ v') ∂(μW.map (rmulM u)) := (lintegral_map hm (rmulM_cont u).measurable).symm
    _ = ∫⁻ h, F (Matrix.of h *ᵥ v') ∂μW := by rw [hU k r z μW hW hfin u hu]
end PI.RhsWLim.W.RI
