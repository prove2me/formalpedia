-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.adDFull_zero_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:16:08.813041+00:00
-- url     : https://prove2.me/submissions/0d86f0e8-86ba-4656-a2fb-db44d03ffe71

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Unique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_PrhoEntryHasDerivAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_uq_offdiag_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open scoped Kronecker
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
variable {ε : Fin n → Bool} {β : Bool}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {X : Matrix (Fin n) (Fin n) ℂ} (hX : X * Jm ε = Jm ε * X) (p k : Fin n × Fin n)
    (hp : ε p.1 = β ∧ ε p.2 = !β) (hk : ¬ (ε k.1 = β ∧ ε k.2 = !β)) : adDFull X p k = 0 := by
  simp only [adDFull, Matrix.sub_apply, Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  by_cases h1 : ε k.1 = β
  · have h2 : ε p.2 ≠ ε k.2 := fun h => hk ⟨h1, by rw [← h]; exact hp.2⟩
    have h3 : p.2 ≠ k.2 := fun h => h2 (by rw [h])
    rw [Matrix.one_apply_ne h3, uq_offdiag_zero hX (Ne.symm h2), mul_zero, mul_zero, sub_zero]
  · have h2 : ε p.1 ≠ ε k.1 := fun h => h1 (by rw [← h]; exact hp.1)
    have h3 : p.1 ≠ k.1 := fun h => h2 (by rw [h])
    rw [Matrix.one_apply_ne h3, uq_offdiag_zero hX h2, zero_mul, zero_mul, sub_zero]
end ReciprocityTheory.ChartRestriction.DS.HW
