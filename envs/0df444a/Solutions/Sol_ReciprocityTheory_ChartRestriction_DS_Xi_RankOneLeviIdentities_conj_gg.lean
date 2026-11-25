-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.conj_gg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:09.208822+00:00
-- url     : https://prove2.me/submissions/61a009b5-ecdf-4955-97e7-81223b6be568

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergDualBaseVectorFormulaAlt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_entry_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_heis_liftVec
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities__Lev_liftVec_1c6a24f5fe56
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_bvec_lev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_goodRowsProjector_apply_eq_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_levPos_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_liftVec_lev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_reflection_mulVec_levelPos


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
variable (c : ℂ) (g : Mat k r') (x : HPar k r')
namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
theorem _root_.solution (hHA : HeisAct) (i j : Fin (2 * r' + k + 1)) :
    (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) (levPos k 1 r' i) (levPos k 1 r' j) = g i j := by
  rw [entry_eq (w0 k r' c * heis0 k r' x * ιLev k 1 r' g), ← mulVec_mulVec, ← mulVec_mulVec, bvec_lev, ιLev_liftVec, heis_liftVec k r' hHA,
    reflection_mulVec_levelPos, Pi.sub_apply, Pi.smul_apply, liftVec_lev, goodRowsProjector_apply_eq_sum, if_neg (by rw [levPos_val]; omega),
    smul_zero, sub_zero, bvec, mulVec_single_one]
  rfl
end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
