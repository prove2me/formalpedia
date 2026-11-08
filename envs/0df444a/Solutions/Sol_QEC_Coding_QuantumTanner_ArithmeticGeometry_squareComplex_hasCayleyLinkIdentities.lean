-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.ArithmeticGeometry.squareComplex_hasCayleyLinkIdentities
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:42:04.773037+00:00
-- url     : https://prove2.me/submissions/412b69a7-d47c-42f9-beaa-b8296d993ab1

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticGeometry
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_constantSets_total_nonconjugacy
import Theorems.Thm_QEC_Coding_QuantumTanner_cayleySquareComplex_hasCayleyLinkIdentities


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.ArithmeticGeometry
open QEC.Coding.ExpanderCodes.QuaternionGenerators
universe v
variable {F K : Type v} [Field F] [Field K] [Fintype K]
namespace QEC.Coding.QuantumTanner.ArithmeticGeometry
theorem _root_.solution (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) :
    (squareComplex f epsilon y hEpsilon hY hOne hTwo).HasCayleyLinkIdentities := by
  unfold squareComplex
  exact cayleySquareComplex_hasCayleyLinkIdentities
    (Subtype.val : LeftIndex f epsilon y hY hOne → ProjectiveGroup (f epsilon) y)
    (Subtype.val : RightIndex f epsilon y hEpsilon hY hOne → ProjectiveGroup (f epsilon) y)
    (leftInverse f epsilon y hEpsilon hY hOne)
    (rightInverse f epsilon y hEpsilon hY hOne)
    Subtype.val_injective Subtype.val_injective (fun _ => rfl) (fun _ => rfl)
    (fun g a b => constantSets_total_nonconjugacy f epsilon y hEpsilon hY hOne hTwo
      a.property b.property g)
end QEC.Coding.QuantumTanner.ArithmeticGeometry
