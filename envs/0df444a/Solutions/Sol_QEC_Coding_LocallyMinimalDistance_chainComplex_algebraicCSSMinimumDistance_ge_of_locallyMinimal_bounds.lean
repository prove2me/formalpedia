-- Prove2me | solution 1 for QEC.Coding.LocallyMinimalDistance.chainComplex_algebraicCSSMinimumDistance_ge_of_locallyMinimal_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:43:11.453765+00:00
-- url     : https://prove2.me/submissions/d5ee5f45-d255-4e5d-b8f0-bc6d43784507

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.Order.Lattice.Nat
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Theorems.Thm_QEC_Coding_LocallyMinimalDistance_chainComplex_cycle_weight_ge_of_locallyMinimal_bound
import Theorems.Thm_QEC_Coding_LocallyMinimalDistance_chainComplex_cocycle_weight_ge_of_locallyMinimal_bound

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LocallyMinimalDistance
universe u v
variable {C : Type*} [AddCommGroup C]
namespace QEC.Coding.LocallyMinimalDistance
theorem _root_.solution
    {F : Type u} {ι κ₀ κ₂ : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (weight : Word F ι → Nat) (lowerBound d : Nat)
    (hweight : ∀ c : Word F ι, weight c ≤ HammingWeight c)
    (hcycles : ∀ c : Word F ι, c ∈ K.middleCycleCode.carrier → c ≠ 0 →
      IsLocallyMinimal weight (elementaryBoundaryMoves K) c →
        lowerBound ≤ weight c)
    (hcocycles : ∀ c : Word F ι, c ∈ K.middleCocycleCode.carrier → c ≠ 0 →
      IsLocallyMinimal weight (elementaryCoboundaryMoves K) c →
        lowerBound ≤ weight c)
    (hminimum : AlgebraicCSSMinimumDistance
      K.firstCoboundaryCheckCode K.middleBoundaryCode d) :
    lowerBound ≤ d := by
  rcases hminimum with ⟨c, hc, hdistance, _⟩
  rw [← hdistance]
  rcases hc with hcX | hcZ
  · have hcCocycle : c ∈ K.middleCocycleCode.carrier := by
      rw [← K.middleBoundaryCode_dual_carrier_eq_middleCocycleCode]
      exact hcX.1
    exact (chainComplex_cocycle_weight_ge_of_locallyMinimal_bound
      K weight lowerBound hcocycles c hcCocycle hcX.2).trans (hweight c)
  · have hcCycle : c ∈ K.middleCycleCode.carrier := by
      rw [← K.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode]
      exact hcZ.1
    exact (chainComplex_cycle_weight_ge_of_locallyMinimal_bound
      K weight lowerBound hcycles c hcCycle hcZ.2).trans (hweight c)
end QEC.Coding.LocallyMinimalDistance
