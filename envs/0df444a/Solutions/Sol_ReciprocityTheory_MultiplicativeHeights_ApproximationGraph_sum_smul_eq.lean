-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.sum_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:30:59.283633+00:00
-- url     : https://prove2.me/submissions/d60a6541-0790-45bc-9ccc-0e59362c5a6b

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
open ComplexConjugate
namespace ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
theorem _root_.solution {r : ℕ} (X : Fin r → Fin r → ℂ) (w : Fin r → ℂ) (c : ℂ) :
    ∑ j, w j • X j = c • w + ∑ j, w j • (X j - c • (Pi.single j 1 : Fin r → ℂ)) := by
  funext k
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib, Pi.single_apply]
  simp [Finset.mul_sum]
  ring
end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
