-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.heisenberg_dual_base_vector_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:41:04.350476+00:00
-- url     : https://prove2.me/submissions/cf6bf47c-8e31-4888-8a7f-35706d5b38d5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergDualBaseVectorFormulaAlt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_hermitian_dual_base_vector_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_hermitian_form_base_vector_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_last_basis_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_liftVec_out


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
theorem _root_.solution (hHA : HeisAct) (x : HPar k r') :
    heis0 k r' x *ᵥ es0 k r' = es0 k r' + liftVec k 1 r' x.1 + hb k r' x.1 x.2 • e0 k r' := by
  rw [show heis0 k r' x = heisG k r' (liftVec k 1 r' x.1) (hb k r' x.1 x.2) from rfl, hHA, hermitian_dual_base_vector_left,
    liftVec_out k r' x.1 _ (Or.inl rfl), star_zero, zero_smul, sub_zero, hermitian_form_base_vector_right, last_basis_apply, if_pos rfl,
    one_smul]
  exact (add_assoc _ _ _).symm
end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
