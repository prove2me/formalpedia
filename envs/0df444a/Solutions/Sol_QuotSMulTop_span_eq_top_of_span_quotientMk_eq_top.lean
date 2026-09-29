-- Prove2me | solution 1 for QuotSMulTop.span_eq_top_of_span_quotientMk_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/7a12137a-2295-56e1-8ede-89ce5e38cedc

import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Regular.RegularSequence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuotSMulTop_span_eq_top_of_span_quotientMk_eq_top

open scoped Pointwise

theorem solution {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsLocalRing R] [Module.Finite R M] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) {ι : Type*} (m : ι → M) (hspan : Submodule.span (R ⧸ Ideal.span {x}) (Set.range fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M)) = ⊤) :
    Submodule.span R (Set.range m) = ⊤ := by
  have h1 : Submodule.span R
      (Set.range fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M)) = ⊤ := by
    rw [← Submodule.restrictScalars_span R (R ⧸ Ideal.span {x}) Ideal.Quotient.mk_surjective,
      hspan, Submodule.restrictScalars_top]
  have h2 : (Submodule.span R (Set.range m)).map
      (Submodule.mkQ (x • ⊤ : Submodule R M)) = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact h1
  rw [Submodule.map_mkQ_eq_top] at h2
  have hjac : Ideal.span {x} ≤ Ideal.jacobson ⊥ :=
    le_trans (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx))
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  refine top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hjac ?_)
  rw [Submodule.ideal_span_singleton_smul, sup_comm, h2]

end S_QuotSMulTop_span_eq_top_of_span_quotientMk_eq_top
end P2MW
export P2MW.S_QuotSMulTop_span_eq_top_of_span_quotientMk_eq_top (solution)
