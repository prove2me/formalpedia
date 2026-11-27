-- Prove2me | solution 1 for ReciprocityTheory.CA.isCM_of_quotient_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:25:53.1717+00:00
-- url     : https://prove2.me/submissions/46b23b37-8601-488d-a1ec-7897f22ad6df

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Unmixed
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_RingKrullDimQuotientOfMemAssociatedPrimes
import Theorems.Thm_ReciprocityTheory_CA_IsCMMod_of_quotSMulTop
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_of_quotSMulTop
import Theorems.Thm_ReciprocityTheory_CA_isCMMod_congr
import Theorems.Thm_ReciprocityTheory_CA_isCM_iff_isCMMod
import Theorems.Thm_ReciprocityTheory_CA_isCM_quotient_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence Pointwise
variable {R : Type*} [CommRing R] [IsLocalRing R]
private theorem isSMulRegular_of_mem_nonZeroDivisors' {x : R} (reg : x ∈ nonZeroDivisors R) :
    IsSMulRegular R x := by
  intro a b hab
  have h0 : (a - b) * x = 0 := by
    simp only [smul_eq_mul] at hab
    rw [sub_mul, mul_comm a, mul_comm b, hab, sub_self]
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp reg).2 _ h0)
end ReciprocityTheory.CA
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence Pointwise
variable {R : Type*} [CommRing R] [IsLocalRing R]
namespace ReciprocityTheory.CA
theorem _root_.solution [IsNoetherianRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (reg : x ∈ nonZeroDivisors R) [IsLocalRing (R ⧸ Ideal.span {x})]
    (h : IsCM (R ⧸ Ideal.span {x})) : IsCM R := by
  exact isCM_iff_isCMMod.mpr (IsCMMod.of_quotSMulTop hx (isSMulRegular_of_mem_nonZeroDivisors' reg)
    ((isCMMod_congr (quotSMulTopEquivQuot' x)).mpr ((isCM_quotient_iff _).mp h)))
end ReciprocityTheory.CA
