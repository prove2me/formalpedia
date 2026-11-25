-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_negSq_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:18:29.322337+00:00
-- url     : https://prove2.me/submissions/502d2884-bd5d-4190-98c3-f8a480033fa3

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
theorem _root_.solution (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : 0 ≤ negSq p u := Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
end ReciprocityTheory.MultiplicativeHeights
