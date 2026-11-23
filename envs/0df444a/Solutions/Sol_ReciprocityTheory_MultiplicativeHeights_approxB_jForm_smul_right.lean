-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_jForm_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:25.654201+00:00
-- url     : https://prove2.me/submissions/9cc6158b-159f-413f-ba5a-29540933635b

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
theorem _root_.solution (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) (a : ℂ) :
    jForm p x (a • y) = a * jForm p x y := by
  simp only [jForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring
end ReciprocityTheory.MultiplicativeHeights
