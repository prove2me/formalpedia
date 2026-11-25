-- Prove2me | solution 1 for PI.RhsWLim.W.continuous_opEmap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:27:47.12281+00:00
-- url     : https://prove2.me/submissions/c7a3538b-ff82-4b04-9976-ef42c3541699

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushE
import Theorems.Thm_PI_RhsWLim_W_continuous_opGen

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
theorem _root_.solution (k r : ℕ) (T' : ℝ) :
    Continuous (fun q : TrE k => opCo k r (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T')) := by

  letI : NormedRing (Mat k r) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Mat k r) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Mat k r) := Matrix.linftyOpNormedAlgebra
  have h1 : Continuous (fun q : TrE k => NormedSpace.exp (opGen k r q)) :=
    NormedSpace.exp_continuous.comp (continuous_opGen k r)
  have h2 : Continuous (fun q : TrE k => NormedSpace.exp (opGen k r q) *ᵥ opBase k r T') :=
    h1.matrix_mulVec continuous_const
  unfold opCo
  exact (continuous_pi (fun i => (continuous_apply (wI k r (Fin.castSucc i))).comp h2)).prodMk
    ((continuous_apply (wI k r (Fin.last k))).comp h2)
end PI.RhsWLim.W
