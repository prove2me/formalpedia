-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.XI.meas_xi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:33:35.730149+00:00
-- url     : https://prove2.me/submissions/1bf38b48-41e6-4797-9340-348c574bcce3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GramReDetLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaNonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_XI_cont_ga

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
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.XI
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Xi.GS ReciprocityTheory.ChartRestriction.DS.Xi.GSB
namespace ReciprocityTheory.ChartRestriction.DS.Xi.XI
theorem _root_.solution (k r : ℕ) (s : Fin (r + 1) → ℝ) : Measurable fun x : Mt k r => xiN k r s (Matrix.of x) := by
  unfold xiN xiR
  refine Measurable.real_toNNReal ?_
  refine Finset.measurable_prod _ fun l _ => ?_
  refine Measurable.pow_const ?_ _
  exact ((cont_ga l).sqrt).measurable
end ReciprocityTheory.ChartRestriction.DS.Xi.XI
