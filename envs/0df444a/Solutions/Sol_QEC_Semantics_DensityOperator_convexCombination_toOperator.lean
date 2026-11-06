-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.convexCombination_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:05:40.271318+00:00
-- url     : https://prove2.me/submissions/02d0b675-8455-478c-aa40-ad2bddec4cee

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Entropy_Convexity

set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open QEC.Semantics.DensityOperator
open scoped BigOperators ComplexOrder
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
namespace QEC.Semantics.DensityOperator
theorem _root_.solution {ι : Type v} (s : Finset ι) (w : ι → ℝ)
    (ρ : ι → DensityOperator H) (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1) :
    (convexCombination s w ρ hw_nonneg hw_sum).toOperator =
      convexCombinationOperator s w ρ :=
  rfl
end QEC.Semantics.DensityOperator
