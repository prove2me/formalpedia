-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.io_conjT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:15:44.253292+00:00
-- url     : https://prove2.me/submissions/3c1298f4-5867-4e66-a1a6-7c0168a94126

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec

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
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
variable {k r' : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (g : Mat k r') : ιLev k 1 r' gᴴ = (ιLev k 1 r' g)ᴴ := by
  ext p q
  rw [conjTranspose_apply]; unfold ιLev
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 <;>
    by_cases hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
  · rw [dif_pos hp, dif_pos hq, dif_pos hq, dif_pos hp, conjTranspose_apply]
  · rw [dif_pos hp, dif_neg hq, dif_neg hq, if_neg (fun h => by subst h; exact hq hp), star_zero]
  · rw [dif_neg hp, dif_pos hq, dif_neg hp, if_neg (fun h => by subst h; exact hp hq), star_zero]
  · rw [dif_neg hp, dif_neg hq]; by_cases h : p = q
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), star_zero]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
