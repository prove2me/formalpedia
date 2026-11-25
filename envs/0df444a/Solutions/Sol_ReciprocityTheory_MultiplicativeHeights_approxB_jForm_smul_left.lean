-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_jForm_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:16:34.652328+00:00
-- url     : https://prove2.me/submissions/234c082a-2164-4a1d-8488-f4964681017a

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
    jForm p (a • x) y = conj a * jForm p x y := by
  simp only [jForm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring
end ReciprocityTheory.MultiplicativeHeights
