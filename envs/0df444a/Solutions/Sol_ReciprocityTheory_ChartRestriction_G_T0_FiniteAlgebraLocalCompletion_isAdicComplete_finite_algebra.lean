-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:26.085796+00:00
-- url     : https://prove2.me/submissions/703f5e75-d688-4e1d-8e32-484ce87b9459

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPrecompleteFiniteModule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_isPrecomplete_finite_module

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
theorem _root_.solution {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (S : Type*) [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsAdicComplete ((maximalIdeal R).map (algebraMap R S)) S := by
  rw [IsAdicComplete.map_algebraMap_iff]
  have := isPrecomplete_finite_module (maximalIdeal R) S
  exact ⟨⟩
end ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
