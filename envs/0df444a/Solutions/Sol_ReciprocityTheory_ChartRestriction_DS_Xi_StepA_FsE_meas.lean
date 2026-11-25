-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.FsE_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:38:21.525842+00:00
-- url     : https://prove2.me/submissions/4ddd2038-6e92-4415-9bc4-dae63f8b9f4c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergRankOneDecomposition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RankOneLeviComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkNegMp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_EIntBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergFactsOfInductiveInput
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_Dl_cont

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution (r : ℕ) (s : Fin (r + 1) → ℝ) : Measurable (fun g : Mt k r => FsE k r s (Matrix.of g)) := by
  unfold FsE
  exact Finset.measurable_prod _ fun l _ =>
    ((Dl_cont k r l).measurable.nnnorm.coe_nnreal_ennreal).pow_const _
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
