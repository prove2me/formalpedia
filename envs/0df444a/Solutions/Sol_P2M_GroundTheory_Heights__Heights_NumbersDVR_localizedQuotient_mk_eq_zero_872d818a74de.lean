-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuotient_mk_eq_zero_872d818a74de
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:41.565952+00:00
-- url     : https://prove2.me/submissions/3914a96d-1fb7-43d5-8ef5-1f234aeff997

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultAtPrimeAtMinimal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
variable {A : Type*} [CommRing A]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (W : Ideal A) [W.IsPrime] (a : A) (s : W.primeCompl)
    (h : LocalizedModule.mk (Ideal.Quotient.mk W a) s = 0) : a ∈ W := by
  rw [← LocalizedModule.zero_mk (1 : W.primeCompl), LocalizedModule.mk_eq] at h
  obtain ⟨u, hu⟩ := h
  rw [smul_zero, smul_zero, one_smul, Submonoid.smul_def, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hu
  exact (‹W.IsPrime›.mem_or_mem hu).resolve_left u.2
end GroundTheory.Heights₂.Heights.NumbersDVR
