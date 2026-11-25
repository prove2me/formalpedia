-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.conj_cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:54:42.300863+00:00
-- url     : https://prove2.me/submissions/e7de81a0-737c-463c-b9d1-abc7c0d63d02

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergDualBaseVectorFormulaAlt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_entry_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_dual_base_vector_eq_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_heisenberg_dual_base_vector_formula
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_goodRowsProjector_apply_eq_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_last_basis_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_levelEmbedding_mulVec_es0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_liftVec_out
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_rankOneMatrix_last_coord


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
theorem _root_.solution (hHA : HeisAct) :
    (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) ⟨2 * (1 + r') + k, by omega⟩ ⟨2 * (1 + r') + k, by omega⟩ =
      c * hb k r' x.1 x.2 := by
  rw [entry_eq (w0 k r' c * heis0 k r' x * ιLev k 1 r' g), ← mulVec_mulVec, ← mulVec_mulVec, ← dual_base_vector_eq_single, levelEmbedding_mulVec_es0, heisenberg_dual_base_vector_formula k r' hHA, rankOneMatrix_last_coord,
    Pi.add_apply, Pi.add_apply, Pi.smul_apply, liftVec_out k r' x.1 _ (Or.inl rfl), goodRowsProjector_apply_eq_sum, last_basis_apply,
    if_neg (by simp only; omega), if_pos rfl]
  simp
end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
