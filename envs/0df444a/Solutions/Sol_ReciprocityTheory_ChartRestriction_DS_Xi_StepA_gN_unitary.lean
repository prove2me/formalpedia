-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.gN_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:38:41.677815+00:00
-- url     : https://prove2.me/submissions/6d1397d9-f531-4277-9a2d-8026535eb5c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DetEqMulMinorOfColZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RankOneLeviComm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_normSq_sum_eq_trace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution (k r : ℕ) {κ : Mat k r} (hκ : κᴴ * κ = 1) (X : Mat k r) : gN (κ * X) = gN X := by
  unfold gN
  congr 1
  have h1 := normSq_sum_eq_trace (κ * X)
  have h2 := normSq_sum_eq_trace X
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul] at h1
  exact_mod_cast h1.trans h2.symm
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
