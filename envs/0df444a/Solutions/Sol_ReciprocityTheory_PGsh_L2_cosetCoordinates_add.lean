-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.cosetCoordinates_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:30:51.148252+00:00
-- url     : https://prove2.me/submissions/81397333-8074-4997-b24d-5c86d1611ac8

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetLeOneOfEntriesIntegral
import Theorems.Thm_ReciprocityTheory_PGsh_L2_cosetCoordinates_expand

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
    (x : N) (k : K) : h3co K β f (x + k) = h3co K β f x ᵥ* h3T K β k := by
  ext l'
  have hw : (fun k' : K => f (x + k + k')) =
      ∑ l, h3co K β f x l • (fun k' : K => β (k + k') l) := by
    ext k'
    rw [show (x + (k : N) + (k' : N)) = x + ((k + k' : K) : N) by simp [add_assoc],
      cosetCoordinates_expand K β hβ f x (k + k')]
    simp [Finset.sum_apply, mul_comm]
  show (β⁻¹ *ᵥ fun k' : K => f (x + k + k')) l' = _
  rw [hw, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.vecMul,
    dotProduct, h3T, Matrix.of_apply]
end ReciprocityTheory.PGsh.L2
