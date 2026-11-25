-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_posSq_add_negSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:21:01.205868+00:00
-- url     : https://prove2.me/submissions/c6ad83a5-2b3b-4be3-9920-6e1c4fca11b2

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
    posSq p u + negSq p u = normSq u := by
  rw [posSq, negSq, normSq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp
end ReciprocityTheory.MultiplicativeHeights
