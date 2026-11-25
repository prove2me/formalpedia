-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_numStandardTable_eq_card_monotone_c3531fff2cb2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:13:12.455498+00:00
-- url     : https://prove2.me/submissions/4f5f689b-4318-47bf-951f-ef625a273cd9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTableEqCardMonotone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.YoungDiagramCombinatorics
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.RestTerms.YoungDiagramCombinatorics
theorem _root_.solution {m : ℕ} (lam : Fin m → ℕ) :
    RestTerms.numStandardTable lam =
      Nat.card {T : RestTerms.youngCells lam ≃ Fin (RestTerms.youngCells lam).card //
        Monotone T} := by
  unfold RestTerms.numStandardTable
  refine Nat.card_congr (Equiv.subtypeEquivRight fun T => ?_)
  constructor
  · intro h p q hpq
    have h' := Prod.le_def.1 (Subtype.coe_le_coe.2 hpq)
    exact h p q h'.1 h'.2
  · intro h p q h1 h2
    exact h (Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨h1, h2⟩))
end GroundTheory.Heights₂.Heights.RestTerms.YoungDiagramCombinatorics
