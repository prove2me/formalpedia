-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_jForm_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:56.596099+00:00
-- url     : https://prove2.me/submissions/6c19c8dc-6d18-42fa-b472-4758848db065

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (p : ℕ) {r : ℕ} (u : Fin r → ℂ) :
    jForm p u u = ((posSq p u - negSq p u : ℝ) : ℂ) := by
  rw [jForm, posSq, negSq, ← Finset.sum_sub_distrib]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.conj_mul']
  by_cases h : (k : ℕ) < p <;> simp [sgn, h]
end ReciprocityTheory.MultiplicativeHeights
