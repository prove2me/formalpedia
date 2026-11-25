-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.hpk_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:28:27.238399+00:00
-- url     : https://prove2.me/submissions/4625c710-5011-4272-a0d6-b2054df5da29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkMulVecMulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_hpk_out
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_hpk_mid

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
theorem _root_.solution (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h]
    simp only [Matrix.mulVec, dotProduct, hpk_out k r h]
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · simp
    · intro j _ hj
      have hj' : j.val ≠ 2 * r + k - i.val := fun hc => hj (Fin.ext hc)
      simp [hj']
    · simp
  · rw [if_neg h]
    simp only [Matrix.mulVec, dotProduct, hpk_mid k r h]
    rw [Finset.sum_eq_single i]
    · by_cases h2 : i.val = r + k <;> simp [h2]
    · intro j _ hj
      have hj' : j.val ≠ i.val := fun hc => hj (Fin.ext hc)
      simp [hj']
    · simp
end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
