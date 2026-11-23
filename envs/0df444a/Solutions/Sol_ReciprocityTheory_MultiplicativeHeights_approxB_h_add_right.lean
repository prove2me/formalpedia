-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_h_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:10.48931+00:00
-- url     : https://prove2.me/submissions/e615188b-fd84-4443-9ddb-f0395f4ba3dd

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
    (x y z : Fin r → K) : S.h x (y + z) = S.h x y + S.h x z := by
  unfold ReciprocityTheory.MultiplicativeHeights.HermForm.h
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
end ReciprocityTheory.MultiplicativeHeights
