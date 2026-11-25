-- Prove2me | solution 1 for PI.RhsWLim.W.HU.pull_sigmaFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:46:42.490993+00:00
-- url     : https://prove2.me/submissions/bbbc1d38-ca7f-457e-ad1c-6982e41f3fb0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Theorems.Thm_PI_RhsWLim_W_HU_inc_memb

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
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.HU
open PI.RhsWLim
variable {k r : ℕ}
namespace PI.RhsWLim.W.HU
theorem _root_.solution (μ : Measure (Mt k r)) [SigmaFinite μ] : SigmaFinite (pull μ) := by
  refine (Measure.FiniteSpanningSetsIn.sigmaFinite (C := Set.univ)
    ⟨fun n => (inc : Gp k r → Mt k r) ⁻¹' spanningSets μ n, fun _ => trivial, fun n => ?_, ?_⟩)
  · rw [pull, inc_memb.comap_apply]
    exact lt_of_le_of_lt (measure_mono (Set.image_preimage_subset _ _)) (measure_spanningSets_lt_top μ n)
  · rw [← Set.preimage_iUnion, iUnion_spanningSets, Set.preimage_univ]
end PI.RhsWLim.W.HU
