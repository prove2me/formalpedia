-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.exists_pow_mem_map_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:18.726484+00:00
-- url     : https://prove2.me/submissions/6aff2929-d62c-4149-878f-6e32e50d98c0

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
    [Algebra R S] [Module.Finite R S] (b : S) (hb : ∀ n : Ideal S, n.IsMaximal → b ∈ n) :
    ∃ N : ℕ, 0 < N ∧ b ^ N ∈ (maximalIdeal R).map (algebraMap R S) := by
  let J := (maximalIdeal R).map (algebraMap R S)
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ J) := Module.Finite.of_restrictScalars_finite R _ _
  have : IsArtinianRing (S ⧸ J) := IsArtinianRing.of_finite (R ⧸ maximalIdeal R) (S ⧸ J)
  obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := S ⧸ J)
  have hmem : Ideal.Quotient.mk J b ∈ (⊥ : Ideal (S ⧸ J)).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro q ⟨-, hq⟩
    have := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective (K := q)
    exact hb _ this
  have h1 : Ideal.Quotient.mk J (b ^ (k + 1)) = 0 := by
    have := Ideal.pow_mem_pow hmem k
    rw [hk, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    rw [pow_succ, map_mul, map_pow, this, zero_mul]
  exact ⟨k + 1, k.succ_pos, Ideal.Quotient.eq_zero_iff_mem.mp h1⟩
end ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
