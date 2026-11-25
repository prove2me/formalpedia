-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.DetB.cl_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:28:14.951133+00:00
-- url     : https://prove2.me/submissions/cd9056b1-197e-4296-b028-c243c93275be

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianLiftIdentities
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_DetB_lipschitzConst_nonneg

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
theorem _root_.solution (k r : ℕ) (l : Fin (r + 1)) : 0 < cl k r l := by
  have := lipschitzConst_nonneg k r
  unfold cl; positivity
end ReciprocityTheory.ChartRestriction.DS.Xi.DetB
