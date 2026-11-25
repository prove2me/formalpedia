-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.XI.cont_gN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:21:16.052823+00:00
-- url     : https://prove2.me/submissions/54a43be2-71fd-4133-b324-67c23123c856

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GramReDetLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaNonneg

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
theorem _root_.solution {k r : ℕ} : Continuous (gN : Mat k r → ℝ) := by
  unfold gN
  refine Continuous.sqrt ?_
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact Complex.continuous_normSq.comp (continuous_id.matrix_elem i j)
end ReciprocityTheory.ChartRestriction.DS.Xi.XI
