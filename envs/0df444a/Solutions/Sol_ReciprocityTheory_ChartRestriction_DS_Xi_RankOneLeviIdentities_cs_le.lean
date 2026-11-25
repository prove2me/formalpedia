-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.cs_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:39:46.105961+00:00
-- url     : https://prove2.me/submissions/57f6c5eb-0eed-4a7f-9de4-3f51b9769ec5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergDualBaseVectorFormulaAlt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_gN_entry
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_hb_im

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
theorem _root_.solution (c : ℂ) (x : HPar k r') (M : Mat k (1 + r'))
    (h : M ⟨2 * (1 + r') + k, by omega⟩ ⟨2 * (1 + r') + k, by omega⟩ = c * hb k r' x.1 x.2) :
    ‖c‖ * |x.2| ≤ gN M := by
  calc ‖c‖ * |x.2| ≤ ‖c‖ * ‖hb k r' x.1 x.2‖ := by
        gcongr
        have := Complex.abs_im_le_norm (hb k r' x.1 x.2)
        rwa [hb_im] at this
    _ = ‖M ⟨2 * (1 + r') + k, by omega⟩ ⟨2 * (1 + r') + k, by omega⟩‖ := by rw [h, norm_mul]
    _ ≤ gN M := gN_entry k _ _ _
end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
