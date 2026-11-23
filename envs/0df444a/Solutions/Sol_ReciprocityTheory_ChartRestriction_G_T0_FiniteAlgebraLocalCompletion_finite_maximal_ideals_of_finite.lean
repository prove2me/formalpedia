-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.finite_maximal_ideals_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:21.88386+00:00
-- url     : https://prove2.me/submissions/7d60f6c4-6915-4ddc-bd16-390e29cc888e

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPrecompleteFiniteModule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_map_maximalIdeal_le_maximal

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
    [Algebra R S] [Module.Finite R S] : {n : Ideal S | n.IsMaximal}.Finite := by
  let J := (maximalIdeal R).map (algebraMap R S)
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ J) := Module.Finite.of_restrictScalars_finite R _ _
  have : IsArtinianRing (S ⧸ J) := IsArtinianRing.of_finite (R ⧸ maximalIdeal R) (S ⧸ J)
  refine ((IsArtinianRing.setOfPred_isMaximal_finite (S ⧸ J)).image
    (Ideal.comap (Ideal.Quotient.mk J))).subset ?_
  intro n hn
  refine ⟨n.map (Ideal.Quotient.mk J), ?_, ?_⟩
  · have hJ : J ≤ n := map_maximalIdeal_le_maximal S n hn
    have : n.IsMaximal := hn
    exact Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by simpa using hJ)
  · have hJ : J ≤ n := map_maximalIdeal_le_maximal S n hn
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hJ
end ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
