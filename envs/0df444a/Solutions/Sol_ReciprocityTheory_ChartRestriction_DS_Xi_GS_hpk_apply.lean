-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GS.hpk_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:01:23.353774+00:00
-- url     : https://prove2.me/submissions/63aa323d-5504-4df2-a402-ce761a5ab1ac

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GS
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {k r : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS
theorem _root_.solution (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = sigI k r i then sgnI k r i else 0 := by
  unfold Hpk sgnI
  simp only [Fin.ext_iff, sigI_val]
  split_ifs <;> first | rfl | (exfalso; omega)
end ReciprocityTheory.ChartRestriction.DS.Xi.GS
