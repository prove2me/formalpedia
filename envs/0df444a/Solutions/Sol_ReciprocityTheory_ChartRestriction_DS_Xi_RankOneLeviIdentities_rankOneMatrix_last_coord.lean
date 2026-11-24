-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.rankOneMatrix_last_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:18:14.885815+00:00
-- url     : https://prove2.me/submissions/08e792b4-df09-4faa-be7b-c56a4b182abb

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_reflection_apply_entries

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
theorem _root_.solution (c : ℂ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    (w0 k r' c *ᵥ u) ⟨2 * (1 + r') + k, by omega⟩ = c * u ⟨0, by omega⟩ := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single ⟨0, by omega⟩]
  · rw [reflection_apply_entries, if_neg (by simp only; omega), if_pos ⟨rfl, rfl⟩]
  · intro b _ hb
    have hb' : b.val ≠ 0 := fun h => hb (Fin.ext h)
    rw [reflection_apply_entries, if_neg (by simp only; omega), if_neg (by simp only; omega),
      if_neg (fun h => absurd h.2.2 (lt_irrefl _)), zero_mul]
  · simp
end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
