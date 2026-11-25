-- Prove2me | solution 1 for PI.RhsWLim.W.continuous_expChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:37:27.409956+00:00
-- url     : https://prove2.me/submissions/2f2d9253-77de-4808-826c-65e72a907f13

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas

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
namespace PI.RhsWLim.W
theorem _root_.solution (k r : ℕ) (S : Set (Mat k r)) :
    Continuous (fun x : lieE S =>
      fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))) i j :
        lieE S → Mt k r) := by
  set n := 2 * r + k + 1
  have hexp : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => NormedSpace.exp A) := by
    let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    have : @CompleteSpace (Matrix (Fin n) (Fin n) ℂ) PseudoMetricSpace.toUniformSpace := by
      let _ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
      exact FiniteDimensional.complete ℂ _
    let _ : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra (R := ℚ)
    exact NormedSpace.exp_continuous
  have hun : Continuous (fun x : EuclideanSpace ℝ (Fin n × Fin n × Bool) => unrealify x) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have hmk : Continuous (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) := Complex.equivRealProdCLM.symm.continuous
    show Continuous (fun x : EuclideanSpace ℝ (Fin n × Fin n × Bool) => (⟨x (i, j, false), x (i, j, true)⟩ : ℂ))
    exact hmk.comp ((PiLp.continuous_apply 2 (fun _ : Fin n × Fin n × Bool => ℝ) (i, j, false)).prodMk
      (PiLp.continuous_apply 2 (fun _ : Fin n × Fin n × Bool => ℝ) (i, j, true)))
  have hall : Continuous (fun x : lieE S =>
      NormedSpace.exp (unrealify (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)))) :=
    (hexp.comp hun).comp continuous_subtype_val
  exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp ((continuous_apply i).comp hall)
end PI.RhsWLim.W
