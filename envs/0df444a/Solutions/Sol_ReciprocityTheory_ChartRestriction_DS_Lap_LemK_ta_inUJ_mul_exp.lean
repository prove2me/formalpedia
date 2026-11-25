-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.ta_inUJ_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:18:47.098599+00:00
-- url     : https://prove2.me/submissions/776d74b5-b5cc-4826-b8b6-4552e1c463fb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_ta_Jm_Jm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_ta_exp_conjT

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
theorem _root_.solution (ε : Fin n → Bool) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X)
    (t : ℝ) : inUJ ε (g * NormedSpace.exp ((t : ℂ) • X)) := by
  unfold inUJ at hg ⊢
  rw [conjTranspose_mul, ta_exp_conjT ε hX t]
  have he : NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X) = 1 := by
    rw [← Matrix.exp_add_of_commute (-((t : ℂ) • X)) ((t : ℂ) • X) ((Commute.refl ((t : ℂ) • X)).neg_left),
      neg_add_cancel, NormedSpace.exp_zero]
  calc Jm ε * NormedSpace.exp (-((t : ℂ) • X)) * Jm ε * gᴴ * Jm ε * (g * NormedSpace.exp ((t : ℂ) • X))
      = Jm ε * NormedSpace.exp (-((t : ℂ) • X)) * Jm ε * (gᴴ * Jm ε * g) * NormedSpace.exp ((t : ℂ) • X) := by
        simp only [mul_assoc]
    _ = Jm ε * NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X) := by
        rw [hg]; simp only [mul_assoc, ta_Jm_Jm]
    _ = Jm ε := by rw [mul_assoc, he, mul_one]
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
