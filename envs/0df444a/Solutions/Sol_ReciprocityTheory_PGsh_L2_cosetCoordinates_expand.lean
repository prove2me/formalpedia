-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.cosetCoordinates_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:02.45301+00:00
-- url     : https://prove2.me/submissions/36f54609-36fe-4cf3-96b4-8a33fe92ced8

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetLeOneOfEntriesIntegral

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
theorem _root_.solution (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det) (f : N → C)
    (x : N) (k : K) : f (x + k) = ∑ l, β k l * h3co K β f x l := by
  have e : β *ᵥ (β⁻¹ *ᵥ fun k' : K => f (x + k')) = fun k' : K => f (x + k') := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hβ, Matrix.one_mulVec]
  exact (congrFun e k).symm
end ReciprocityTheory.PGsh.L2
