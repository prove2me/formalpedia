-- Prove2me | solution 1 for UpperTheory.Reformulated.B.KudlaSiegelWeil.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:54:08.004786+00:00
-- url     : https://prove2.me/submissions/03c31830-532f-46c2-b23b-d55e59599dc7

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_KudlaSiegelWeil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.KudlaSiegelWeil
theorem _root_.solution :
    ∀ {K : Type} [inst : Field K] [NumberField K] {V : Type} [inst_2 : AddCommGroup V]
    [inst_3 : _root_.Module K V] [inst_4 : _root_.Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (L : Submodule (NumberField.RingOfIntegers K) V) {y : V},
    y ∈ Submodule.span K (↑L : Set V) →
      ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • y ∈ L := by
  intro K _ _ V _ _ _ _ L y hy
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers K)) K (↑L : Set V) y hy
  refine ⟨t, nonZeroDivisors.ne_zero t.2, ?_⟩
  rw [Submodule.span_eq] at ht
  exact ht
end UpperTheory.Reformulated.B.KudlaSiegelWeil
