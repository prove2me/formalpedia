-- Prove2me | solution 1 for PI.ArtSch.Glue.v_l_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:34:07.721489+00:00
-- url     : https://prove2.me/submissions/97cd5f6b-0eac-4b64-a09d-81ad62a5f696

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationGluing_ValbLeOfCoeffEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ArtSch PI.ArtSch.Glue
open scoped NNReal
noncomputable section
variable {l : ℕ} [hl : Fact l.Prime]
namespace PI.ArtSch.Glue
theorem _root_.solution : (PadicComplex.valued l).v ((l : ℕ) : PadicComplex l) < 1 := by
  have hv := PadicComplexInt.integers l
  have hnu : ¬ IsUnit ((l : ℕ) : OC l) := Fact.out
  have h1 := hv.map_le_one ((l : ℕ) : OC l)
  have h2 : (PadicComplex.valued l).v (algebraMap (OC l) (PadicComplex l) ((l : ℕ) : OC l)) ≠ 1 :=
    fun h => hnu (hv.isUnit_iff_valuation_eq_one.mpr h)
  rw [map_natCast] at h1 h2
  exact lt_of_le_of_ne h1 h2
end PI.ArtSch.Glue
