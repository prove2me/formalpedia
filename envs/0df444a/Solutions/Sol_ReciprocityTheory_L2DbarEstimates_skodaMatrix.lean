-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.skodaMatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:08:14.767164+00:00
-- url     : https://prove2.me/submissions/26220034-dddb-4685-bc21-6754b903a689

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_projPerp_mulVec_idem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_sum_normSq_projPerp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_normSq_sum_mul_le
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_trace_mul_transpose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {p : ℕ}
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution : SkodaMatrixStatement := by
  intro p n g J V hg
  have hPu : ∀ i, projPerp g *ᵥ ((projPerp g * J) *ᵥ V i) = (projPerp g * J) *ᵥ V i := by
    intro i
    rw [← Matrix.mulVec_mulVec]
    exact projPerp_mulVec_idem hg _
  have htr : trace (projPerp g * J * Vᵀ) =
      ∑ x : Fin p × Fin p, projPerp g x.1 x.2 * ((projPerp g * J) *ᵥ V x.1) x.2 := by
    rw [trace_mul_transpose, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (congrFun (hPu i) i).symm
  rw [htr]
  refine (normSq_sum_mul_le _ _ _).trans ?_
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, sum_normSq_projPerp hg]
  exact le_rfl
end ReciprocityTheory.L2DbarEstimates
