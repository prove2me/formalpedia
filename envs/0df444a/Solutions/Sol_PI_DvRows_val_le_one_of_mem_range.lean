-- Prove2me | solution 1 for PI.DvRows.val_le_one_of_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:40:37.993001+00:00
-- url     : https://prove2.me/submissions/2ab1f744-9742-4ba6-940d-5ce96b6c436c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_ValLeOneOfMemRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace PI.DvRows
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (x : K)
    (hx : x ∈ Set.range (algebraMap (𝓞 K) K)) : w.valuation K x ≤ 1 := by
  obtain ⟨r, rfl⟩ := hx
  exact w.valuation_le_one r
end PI.DvRows
