-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_normSq_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:13:15.877974+00:00
-- url     : https://prove2.me/submissions/3304da80-7c8b-4997-8586-405353c161cb

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
theorem _root_.solution {r : ℕ} (j : Fin r) (R : ℝ) :
    normSq ((R : ℂ) • (Pi.single j 1 : Fin r → ℂ)) = R ^ 2 := by
  unfold normSq
  rw [Finset.sum_eq_single j]
  · simp [sq_abs]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp
end ReciprocityTheory.MultiplicativeHeights
