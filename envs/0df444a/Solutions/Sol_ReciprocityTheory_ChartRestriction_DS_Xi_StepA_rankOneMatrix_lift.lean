-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.rankOneMatrix_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:29:29.223269+00:00
-- url     : https://prove2.me/submissions/23749f7f-d449-4a00-9ceb-617e0cb4ed61

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_UHMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GoodRowsProjectorApplyEqSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_sum_split
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_mp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_zero_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_lift_last
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_rankOneMatrix_middle_coord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_mp
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_zero_pos
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.Xi.StepA.lift_last

set_option autoImplicit false
noncomputable section
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution (c : ℂ) (v : Fin (2 * r' + k + 1) → ℂ) : w0 k r' c *ᵥ liftVec k 1 r' v = liftVec k 1 r' v := by
  funext p
  simp only [mulVec, dotProduct]
  rw [sum_split k r']
  simp only [lift_zero_pos, lift_last, lift_mp, rankOneMatrix_middle_coord, mul_zero, add_zero, zero_add, ite_mul, one_mul,
    zero_mul]
  simp only [liftVec]
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · rw [dif_pos hp, Finset.sum_eq_single (⟨p.val - 1, by omega⟩ : Fin (2 * r' + k + 1))]
    · rw [if_pos]
      dsimp only
      omega
    · intro b _ hb
      rw [if_neg]
      intro h
      apply hb
      ext
      dsimp only
      omega
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [dif_neg hp]
    apply Finset.sum_eq_zero
    intro j _
    have hj := j.isLt
    rw [if_neg]
    intro h
    apply hp
    omega
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
