-- Prove2me | solution 1 for PI.DvRows.mem_iff_vAdd_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:04.802179+00:00
-- url     : https://prove2.me/submissions/af126535-54e2-4266-9367-1b33857ce28f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated

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
open Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K]
namespace PI.DvRows
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K} (hr : r ≠ 0) :
    r ∈ w.asIdeal ↔ 0 < vAdd w (algebraMap (𝓞 K) K r) := by
  rw [← HeightOneSpectrum.intValuation_lt_one_iff_mem]
  unfold vAdd
  rw [HeightOneSpectrum.valuation_of_algebraMap, w.intValuation_eq_exp_neg_multiplicity hr,
    WithZero.log_exp, neg_neg, ← WithZero.exp_zero, WithZero.exp_lt_exp, neg_lt_zero]
end PI.DvRows
