-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.liftVec_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:11:48.93737+00:00
-- url     : https://prove2.me/submissions/eb77933a-e05b-4c67-998b-73796b239857

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_liftVec_apply

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
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
theorem _root_.solution (z : Fin (2 * r' + k + 1) → ℂ) (i : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' z (levPos k 1 r' i) = z i := by
  rw [liftVec_apply, dif_pos (by simp [levPos]; omega)]
  congr 1
end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
