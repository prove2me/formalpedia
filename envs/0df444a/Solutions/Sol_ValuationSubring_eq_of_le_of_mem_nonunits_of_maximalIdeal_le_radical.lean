-- Prove2me | solution 1 for ValuationSubring.eq_of_le_of_mem_nonunits_of_maximalIdeal_le_radical
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/31ed3e99-34f9-59a9-ad25-e99c5f6ed40f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_eq_of_le_of_mem_nonunits_of_maximalIdeal_le_radical

set_option autoImplicit false

theorem solution
    {K : Type*} [Field K] (V W : ValuationSubring K) (hVW : V ≤ W)
    (x : ↥V) (hxW : (x : K) ∈ W.nonunits)
    (hrad : IsLocalRing.maximalIdeal ↥V ≤ (Ideal.span {x}).radical) :
    V = W := by
  have hxP : x ∈ V.idealOfLE W hVW := by
    have h1 : ((V.inclusion W hVW x : ↥W) : K) ∈ W.nonunits := hxW
    exact Ideal.mem_comap.mpr (ValuationSubring.coe_mem_nonunits_iff.mp h1)
  have hle : IsLocalRing.maximalIdeal ↥V ≤ V.idealOfLE W hVW := by
    refine le_trans hrad ?_
    refine (Ideal.IsPrime.radical_le_iff inferInstance).mpr ?_
    exact (Ideal.span_singleton_le_iff_mem _).mpr hxP
  have heq : V.idealOfLE W hVW = IsLocalRing.maximalIdeal ↥V :=
    le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) hle
  have key : ∀ (P : Ideal ↥V) (hP : P.IsPrime), P = IsLocalRing.maximalIdeal ↥V →
      @ValuationSubring.ofPrime K _ V P hP = V := by
    rintro P hP rfl
    exact ValuationSubring.ofPrime_top V
  have h2 : V.ofPrime (V.idealOfLE W hVW) = W := ValuationSubring.ofPrime_idealOfLE V W hVW
  rw [key _ _ heq] at h2
  exact h2

end S_ValuationSubring_eq_of_le_of_mem_nonunits_of_maximalIdeal_le_radical
end P2MW
export P2MW.S_ValuationSubring_eq_of_le_of_mem_nonunits_of_maximalIdeal_le_radical (solution)
