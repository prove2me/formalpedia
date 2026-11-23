-- Prove2me | solution 1 for PI.DvRows.val_eq_one_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:11.574815+00:00
-- url     : https://prove2.me/submissions/e977f338-c3a1-4c6a-98df-82f860570cad

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (s : 𝓞 K) (hs : s ∉ w.asIdeal) :
    w.valuation K (algebraMap (𝓞 K) K s) = 1 := by
  refine le_antisymm (w.valuation_le_one s) ?_
  by_contra hlt
  exact hs ((w.valuation_lt_one_iff_mem s).1 (not_le.1 hlt))
end PI.DvRows
