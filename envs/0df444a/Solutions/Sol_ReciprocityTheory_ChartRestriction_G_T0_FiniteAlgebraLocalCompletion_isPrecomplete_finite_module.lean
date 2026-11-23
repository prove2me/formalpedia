-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:16.895312+00:00
-- url     : https://prove2.me/submissions/44864974-0ea4-488d-90cc-07795f0a2595

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019
import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPrecompleteFiniteModule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
open IsLocalRing Polynomial
namespace ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
theorem _root_.solution {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  first | exact _root_.P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019 .. | (apply _root_.P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019 <;> assumption) | (intros; apply _root_.P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019 <;> assumption) | (apply @_root_.P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019 <;> assumption) | (intros; apply @_root_.P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019 <;> assumption) | (apply @_root_.P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019 <;> first | assumption | infer_instance)
end ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
