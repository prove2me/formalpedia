-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.matLin_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:12.036173+00:00
-- url     : https://prove2.me/submissions/87a9a9fc-58bf-4cc5-b698-781f19e998a4

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegG
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegT
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_matLin_apply

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ}
    (Q : Matrix (Fin r) (Fin r) K) (hQ : Q.det ≠ 0) : Function.Injective (matLin Q) := by
  intro x y hxy
  rw [matLin_apply, matLin_apply] at hxy
  have hu : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).2 (isUnit_iff_ne_zero.2 hQ)
  exact (Matrix.mulVec_injective_iff_isUnit.2 hu) hxy
end ReciprocityTheory.MultiplicativeHeights.SemiPt
