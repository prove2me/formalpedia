-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_normSq_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:13:12.316665+00:00
-- url     : https://prove2.me/submissions/0333a56e-c282-43e0-8769-d9140661cc85

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
theorem _root_.solution {r : ℕ} (u : Fin r → ℂ) : 0 ≤ normSq u := Finset.sum_nonneg fun k _ => by positivity
end ReciprocityTheory.MultiplicativeHeights
