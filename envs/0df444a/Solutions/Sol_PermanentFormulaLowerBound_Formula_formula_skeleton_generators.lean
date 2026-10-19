-- Prove2me | solution 1 for PermanentFormulaLowerBound.Formula.formula_skeleton_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/d7e154c6-e835-4ce9-8426-dc34dc1e03eb

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_Formula_contractedSkeletonRootGenerators_card_le
import Theorems.Thm_PermanentFormulaLowerBound_Formula_contractedSkeletonRootGenerators_coeff_mem

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.Formula
variable {Y : Type u} {Z : Type v} {F : Type w}
variable [Field F]
namespace PermanentFormulaLowerBound.Formula
theorem _root_.solution
    (f : Formula (Y ⊕ Z) F) (hmarked : 0 < yLeafCount f) :
    ∃ s : Finset (FractionRing (MvPolynomial Z F)),
      s.card ≤ 4 * yLeafCount f - 2 ∧
        ∀ α : Y →₀ ℕ,
          algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
            (MvPolynomial.coeff α (splitEval f)) ∈
              IntermediateField.adjoin F (s : Set _) := by
  let w := contractedSkeleton f hmarked
  refine ⟨contractedSkeletonRootGenerators w,
    contractedSkeletonRootGenerators_card_le w hmarked, ?_⟩
  exact contractedSkeletonRootGenerators_coeff_mem w
end PermanentFormulaLowerBound.Formula
