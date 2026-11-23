-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.sqNorm_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:10.340774+00:00
-- url     : https://prove2.me/submissions/c61fc8ad-acdd-48a9-89de-1a4646ccdc8a

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix

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
theorem _root_.solution {g : Fin p → ℂ} (hg : g ≠ 0) : 0 < sqNorm g := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hg
  unfold sqNorm
  exact lt_of_lt_of_le (Complex.normSq_pos.mpr hi)
    (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (g j)) (Finset.mem_univ i))
end ReciprocityTheory.L2DbarEstimates
