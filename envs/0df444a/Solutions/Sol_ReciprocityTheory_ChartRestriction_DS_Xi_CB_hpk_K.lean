-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.CB.hpk_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:51.21915+00:00
-- url     : https://prove2.me/submissions/6dc2ec0b-bc42-43a9-8120-d0687b47d6a7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiIntH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TLeftH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiRNonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_CB_hpk_conjT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_hpk_sq


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
theorem _root_.solution : Hpk k r ∈ Kset k r := by
  have h2 := HermitianLiftIdentities.hpk_sq (k := k) (r := r)
  refine ⟨?_, ?_⟩
  · show (Hpk k r)ᴴ * Hpk k r * Hpk k r = Hpk k r
    rw [hpk_conjT, Matrix.mul_assoc, h2, Matrix.mul_one]
  · rw [hpk_conjT, h2]
end ReciprocityTheory.ChartRestriction.DS.Xi.CB
