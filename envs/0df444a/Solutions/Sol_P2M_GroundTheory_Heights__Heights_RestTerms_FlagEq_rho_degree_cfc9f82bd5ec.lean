-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_rho_degree_cfc9f82bd5ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:51:42.471111+00:00
-- url     : https://prove2.me/submissions/23a9958c-1431-4cb2-b333-ecf6053efc91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoeffRenameProdCongrRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.FlagEq
variable {f N : ℕ}
namespace GroundTheory.Heights₂.Heights.RestTerms.FlagEq
theorem _root_.solution (f N : ℕ) : (rho f N).degree = f * (N * (N - 1) / 2) := by
  rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  simp only [rho, Finsupp.coe_equivFunOnFinite_symm, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N]
  have h := sum_range_reflect (fun i => i) N
  rw [h, sum_range_id]
end GroundTheory.Heights₂.Heights.RestTerms.FlagEq
