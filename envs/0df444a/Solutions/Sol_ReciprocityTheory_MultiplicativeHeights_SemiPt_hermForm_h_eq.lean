-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.hermForm_h_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:26.868394+00:00
-- url     : https://prove2.me/submissions/3bf138c0-114d-40cf-abdf-0506a6a67f99

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegG
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) : S.h x y = formM S.c S.G x y := by
  unfold HermForm.h formM
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
end ReciprocityTheory.MultiplicativeHeights.SemiPt
