-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.tt_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:15:54.983588+00:00
-- url     : https://prove2.me/submissions/74137579-7f97-4eb3-bd6a-bfa3872ab0b8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LevelDeterminantOfTriangularChange

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
variable (τ : Matrix (Fin (r' + 1)) (Fin (r' + 1)) ℂ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (hτ : τ.BlockTriangular id) : (tt τ).BlockTriangular id := by
  intro i j hij
  simp only [id] at hij
  rw [Fin.lt_iff_val_lt_val] at hij
  unfold tt
  by_cases hi : i.val = 0
  · omega
  · rw [if_neg hi]
    by_cases hj : j.val = 0
    · rw [dif_pos hj]
    · rw [dif_neg hj]
      apply hτ
      simp only [id, Fin.mk_lt_mk]
      omega
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
