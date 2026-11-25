-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_h_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:16:31.646868+00:00
-- url     : https://prove2.me/submissions/01d3246e-4e3b-4797-bdb5-797b0bf3d8fa

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
    (x y : Fin r → K) (a : K) : S.h (a • x) y = S.c a * S.h x y := by
  unfold ReciprocityTheory.MultiplicativeHeights.HermForm.h
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul]
  ring
end ReciprocityTheory.MultiplicativeHeights
