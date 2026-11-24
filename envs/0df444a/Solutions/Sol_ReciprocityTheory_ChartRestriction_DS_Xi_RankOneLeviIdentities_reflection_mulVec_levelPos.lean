-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.reflection_mulVec_levelPos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:18:16.563928+00:00
-- url     : https://prove2.me/submissions/d9578b8d-d088-409a-bc22-8214c03b5223

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_levPos_val
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
theorem _root_.solution (c : ℂ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) (i : Fin (2 * r' + k + 1)) :
    (w0 k r' c *ᵥ u) (levPos k 1 r' i) = u (levPos k 1 r' i) := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single (levPos k 1 r' i)]
  · rw [reflection_apply_entries, if_neg (by rw [levPos_val]; omega), if_neg (by rw [levPos_val]; omega),
      if_pos ⟨rfl, by rw [levPos_val]; omega, by rw [levPos_val]; omega⟩, one_mul]
  · intro b _ hb
    rw [reflection_apply_entries, if_neg (by rw [levPos_val]; omega), if_neg (by rw [levPos_val]; omega),
      if_neg (fun h => hb h.1.symm), zero_mul]
  · simp
end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
