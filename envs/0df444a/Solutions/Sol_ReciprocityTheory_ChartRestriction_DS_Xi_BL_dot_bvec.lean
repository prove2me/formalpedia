-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.dot_bvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:52:48.39697+00:00
-- url     : https://prove2.me/submissions/ed41c394-421a-4305-b8d5-837913739c29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf

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
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (i : Fin n) (x : Fin n → ℂ) : star (bvec i) ⬝ᵥ x = x i := by
  unfold dotProduct
  rw [Finset.sum_eq_single i]
  · simp [bvec]
  · intro b _ hb; simp [bvec, hb]
  · intro h; exact absurd (Finset.mem_univ _) h
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
