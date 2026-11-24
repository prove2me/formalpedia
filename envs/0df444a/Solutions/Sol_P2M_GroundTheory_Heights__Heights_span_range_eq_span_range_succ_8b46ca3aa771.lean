-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_span_range_eq_span_range_succ_8b46ca3aa771
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:51.440622+00:00
-- url     : https://prove2.me/submissions/e7c96d49-22df-4fc6-835e-fd406c8bc942

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLengthParameters
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedQuotient
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMLengthParameters

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open IsLocalRing
universe u
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R : Type*} [CommRing R] {k : ℕ} (z : Fin (k + 1) → R) (h0 : z 0 = 0) :
    Ideal.span (Set.range z) = Ideal.span (Set.range fun j : Fin k => z j.succ) := by
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_mono ?_)
  · rintro _ ⟨i, rfl⟩
    cases i using Fin.cases with
    | zero => rw [h0]; exact Ideal.zero_mem _
    | succ j => exact Ideal.subset_span ⟨j, rfl⟩
  · rintro _ ⟨j, rfl⟩
    exact ⟨j.succ, rfl⟩
end GroundTheory.Heights₂.Heights
