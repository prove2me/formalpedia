-- Prove2me | solution 1 for PI.DvRows.vAdd_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:36:39.695509+00:00
-- url     : https://prove2.me/submissions/b6b25056-acce-4d07-876d-30116f5143e6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LocFree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Adapted
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pairing

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
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K]
namespace PI.DvRows
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (T : 𝓞 K) (hT : T ∉ w.asIdeal) :
    vAdd w (algebraMap (𝓞 K) K T) = 0 := by
  have h1 : w.valuation K (algebraMap (𝓞 K) K T) = 1 := by
    refine le_antisymm (w.valuation_le_one T) ?_
    by_contra hlt
    exact hT ((w.valuation_lt_one_iff_mem T).1 (not_le.1 hlt))
  unfold vAdd
  rw [h1, WithZero.log_one, neg_zero]
end PI.DvRows
