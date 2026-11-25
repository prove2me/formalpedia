-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lev_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:04:04.90944+00:00
-- url     : https://prove2.me/submissions/01310870-f925-4cf5-833c-e9e3f0324c7a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DetEqMulMinorOfColZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RankOneLeviComm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lev_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lev_conjT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lev_mem

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
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution {κ : Mat k r'} (hκ : κ ∈ Kset k r') : ιLev k 1 r' κ ∈ Kset k (1 + r') := by
  refine ⟨lev_mem k r' hκ.1, ?_⟩
  rw [lev_conjT, ← lev_mul, hκ.2, lev_one]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
