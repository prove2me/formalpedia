-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.hpk_mulVec_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:42:39.787866+00:00
-- url     : https://prove2.me/submissions/9ad9e2a1-b673-4e1c-a119-86e843409d65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkMulVecMulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_hpk_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_hpk_mulVec


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
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
theorem _root_.solution (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  funext i
  have hi := i.isLt
  rw [hpk_mulVec]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h, hpk_mulVec, if_pos (by dsimp only; omega)]
    congr 1
    ext
    dsimp only
    omega
  · rw [if_neg h]
    split_ifs with h2
    · rw [hpk_mulVec, if_neg h, if_pos h2, neg_neg]
    · rw [hpk_mulVec, if_neg h, if_neg h2]
end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
