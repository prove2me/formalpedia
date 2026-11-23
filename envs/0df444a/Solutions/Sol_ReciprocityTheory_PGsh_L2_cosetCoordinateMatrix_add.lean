-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.cosetCoordinateMatrix_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:40.958208+00:00
-- url     : https://prove2.me/submissions/807b0321-cde3-4a99-9413-21849804e131

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetLeOneOfEntriesIntegral
import Theorems.Thm_ReciprocityTheory_PGsh_L2_cosetCoordinates_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det) (f : K → N → C)
    (x : N) (k : K) : h3mm K β f (x + k) = h3mm K β f x * h3T K β k := by
  ext j l'
  simp only [h3mm, Matrix.of_apply, Matrix.mul_apply]
  rw [cosetCoordinates_add K β hβ (f j) x k]
  simp [Matrix.vecMul, dotProduct]
end ReciprocityTheory.PGsh.L2
