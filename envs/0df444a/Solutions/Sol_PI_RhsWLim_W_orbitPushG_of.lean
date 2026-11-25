-- Prove2me | solution 1 for PI.RhsWLim.W.orbitPushG_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:20:26.506895+00:00
-- url     : https://prove2.me/submissions/28db29fb-d959-46bd-8469-8608e15e1597

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolURatio
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstPair
import Theorems.Thm_PI_RhsWLim_W_rmulM_cont
import Theorems.Thm_PI_RhsWLim_W_continuous_coords

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
theorem _root_.solution (hO : OrbitPush) (hT : TransW) (hU : UnimodW) : OrbitPushG := by
  intro k r z' hk hz' hT' νg hG f hf
  obtain ⟨p, hp, hpz⟩ := hT k r z' hz' hT'
  set zs := ((Real.sqrt (Tz k r z') : ℂ) • wLast k r) with hzs
  have hFm := hf.comp (continuous_coords (k := k) (r := r) zs).measurable
  have e : ∀ x : Mt k r, Matrix.of x *ᵥ z' = Matrix.of (rmulM p x) *ᵥ zs := by
    intro x
    rw [← hpz]
    show Matrix.of x *ᵥ (p *ᵥ zs) = (Matrix.of x * p) *ᵥ zs
    rw [Matrix.mulVec_mulVec]
  calc ∫⁻ x, f (fun i => (Matrix.of x *ᵥ z') (wI k r (Fin.castSucc i)),
          (Matrix.of x *ᵥ z') (wI k r (Fin.last k))) ∂νg
      = ∫⁻ x, (fun y : Mt k r => f (fun i => (Matrix.of y *ᵥ zs) (wI k r (Fin.castSucc i)),
          (Matrix.of y *ᵥ zs) (wI k r (Fin.last k)))) (rmulM p x) ∂νg := by
        refine lintegral_congr fun x => ?_
        simp only [e x]
    _ = ∫⁻ y, f (fun i => (Matrix.of y *ᵥ zs) (wI k r (Fin.castSucc i)),
          (Matrix.of y *ᵥ zs) (wI k r (Fin.last k))) ∂(νg.map (rmulM p)) :=
        (lintegral_map hFm (rmulM_cont p).measurable).symm
    _ = _ := by
        rw [hU k r νg hk hG p hp]
        exact hO k r (Tz k r z') hk hT' νg hG f hf
end PI.RhsWLim.W
