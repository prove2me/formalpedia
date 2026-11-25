-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_h_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:16:33.192199+00:00
-- url     : https://prove2.me/submissions/b0b08fb8-9897-410c-8929-d844675e8c40

import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisB

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
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) (a : K) : S.h x (a • y) = a * S.h x y := by
  unfold ReciprocityTheory.MultiplicativeHeights.HermForm.h
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  ring
end ReciprocityTheory.MultiplicativeHeights
