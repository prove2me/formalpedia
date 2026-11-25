-- Prove2me | solution 1 for QPK.ennreal_le_one_of_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:03.376534+00:00
-- url     : https://prove2.me/submissions/dcbd1da6-1edb-4518-aea9-71e1b3ca1db6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarMeasureUniqueness
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_ConjugationInvariantMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Topology
open scoped ENNReal
open QPK
namespace QPK
theorem _root_.solution {d M : ℝ≥0∞} (hdt : d ≠ ⊤) (hM : M ≠ ⊤)
    (h : ∀ k : ℕ, d ^ k ≤ M) : d ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  lift d to NNReal using hdt
  lift M to NNReal using hM
  have h1 : (1 : NNReal) < d := by exact_mod_cast hlt
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt h1).eventually_gt_atTop M).exists
  have h2 := h k
  rw [← ENNReal.coe_pow, ENNReal.coe_le_coe] at h2
  exact absurd h2 (not_le.mpr hk)
end QPK
