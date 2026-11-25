-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities__Lev_mulVec_890cec92174f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:27:52.573667+00:00
-- url     : https://prove2.me/submissions/a761e619-7021-415e-bd26-d5ccb345d85d

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_levPos_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_sum_lev

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
theorem _root_.solution (g : Mat k r') (u : Fin (2 * (1 + r') + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1)) :
    (ιLev k 1 r' g *ᵥ u) p = if h : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 then
      (g *ᵥ fun j => u (levPos k 1 r' j)) ⟨p.val - 1, by omega⟩ else u p := by
  simp only [mulVec, dotProduct]
  by_cases h : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · rw [dif_pos h, sum_lev k r']
    · apply Finset.sum_congr rfl
      intro j _
      have hj : 1 ≤ (levPos k 1 r' j).val ∧ (levPos k 1 r' j).val < 2 * r' + k + 1 + 1 := by
        rw [levPos_val]; omega
      simp only [ιLev, dif_pos h, dif_pos hj]
      congr 2
    · intro q hq
      simp only [ιLev, dif_pos h, dif_neg hq, zero_mul]
  · rw [dif_neg h]
    simp only [ιLev, dif_neg h]
    rw [Finset.sum_eq_single p]
    · simp
    · intro b _ hb; rw [if_neg (fun e => hb e.symm)]; simp
    · simp
end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
