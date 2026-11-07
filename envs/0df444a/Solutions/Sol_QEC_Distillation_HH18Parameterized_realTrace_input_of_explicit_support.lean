-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.realTrace_input_of_explicit_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:20:45.393199+00:00
-- url     : https://prove2.me/submissions/11135fe1-2399-4355-b3e0-7a5638002ea8

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_EndpointSupport

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Semantics
open scoped BigOperators
universe u
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {ι H : Type u} (support : Finset ι)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (input : Operator H) (inputSummand : ι → Operator H) (realSummand : ι → ℝ)
    (hinput : input = support.sum inputSummand)
    (hpointwise : ∀ i, Complex.re (LinearMap.trace Complex H (inputSummand i)) =
      realSummand i) :
    Complex.re (LinearMap.trace Complex H input) = support.sum realSummand := by
  rw [hinput, map_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  exact hpointwise i
end QEC.Distillation.HH18Parameterized
