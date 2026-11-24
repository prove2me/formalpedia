-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.gN_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:13:00.463997+00:00
-- url     : https://prove2.me/submissions/29e75bb5-a417-40fb-a66e-99cac1ec4e50

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DetEqMulMinorOfColZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RankOneLeviComm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution (k r : ℕ) : Continuous (fun g : Mat k r => gN g) := by
  unfold gN
  exact Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _
    fun j _ => Complex.continuous_normSq.comp (continuous_id.matrix_elem i j))
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
