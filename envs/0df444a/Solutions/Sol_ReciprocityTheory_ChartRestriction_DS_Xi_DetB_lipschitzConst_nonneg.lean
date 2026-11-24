-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.DetB.lipschitzConst_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:36:36.928588+00:00
-- url     : https://prove2.me/submissions/32db9f32-4a4e-4d0e-a755-22aa5df4b6ef

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianLiftIdentities
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_DetB_cst_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.DetB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.DetB
theorem _root_.solution (k r : ℕ) : 0 ≤ K0 k r :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => cst_nonneg _ _ _
end ReciprocityTheory.ChartRestriction.DS.Xi.DetB
