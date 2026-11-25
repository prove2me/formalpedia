-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.CB.xiR_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:45:44.616356+00:00
-- url     : https://prove2.me/submissions/b0e0e47b-3e1f-4b36-81e6-eac49a1d14c3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiIntH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TLeftH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiRNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.CB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Xi.GS
variable {k r : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.CB
theorem _root_.solution (s : Fin (r + 1) → ℝ) (x : Mat k r) : 0 ≤ xiR k r s x :=
  Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _
end ReciprocityTheory.ChartRestriction.DS.Xi.CB
