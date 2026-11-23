-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.map_maximalIdeal_le_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:04.725674+00:00
-- url     : https://prove2.me/submissions/c9f38151-161d-4811-b1f8-bcb317c31bc8

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
theorem _root_.solution {R : Type*} [CommRing R] [IsLocalRing R] (S : Type*) [CommRing S]
    [Algebra R S] [Module.Finite R S] (n : Ideal S) (hn : n.IsMaximal) :
    (maximalIdeal R).map (algebraMap R S) ≤ n := by
  rw [Ideal.map_le_iff_le_comap]
  have : (n.comap (algebraMap R S)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n
  exact (IsLocalRing.eq_maximalIdeal this).ge
end ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
