-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GS.gram_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:58:08.638537+00:00
-- url     : https://prove2.me/submissions/2edf9211-11fd-4f18-9aea-bb7987034e3a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix InnerProductSpace
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GS
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {n m : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS
theorem _root_.solution (w : Fin m → EuclideanSpace ℂ (Fin n)) (τ : Matrix (Fin m) (Fin m) ℂ) :
    gram (fun a => ∑ b, τ b a • w b) = τᴴ * gram w * τ := by
  ext a b
  simp only [gram, of_apply, mul_apply, conjTranspose_apply, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  simp only [starRingEnd_apply]; ring
end ReciprocityTheory.ChartRestriction.DS.Xi.GS
