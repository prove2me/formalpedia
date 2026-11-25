-- Prove2me | solution 1 for ReciprocityTheory.CA.IsCM.quotient_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:06:44.772688+00:00
-- url     : https://prove2.me/submissions/b642344b-d3d3-48a9-8599-1237f36bc397

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Unmixed
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_RingKrullDimQuotientOfMemAssociatedPrimes
import Theorems.Thm_ReciprocityTheory_CA_IsCMMod_quotSMulTop
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_quotSMulTop
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
namespace IsCM
theorem _root_.solution (h : IsCM R) {x : R} (hx : x ∈ maximalIdeal R)
    (reg : x ∈ nonZeroDivisors R) [IsLocalRing (R ⧸ Ideal.span {x})] :
    IsCM (R ⧸ Ideal.span {x}) := by
  haveI : IsNoetherianRing R := h.1
  exact (isCM_quotient_iff _).mpr ((isCMMod_congr (quotSMulTopEquivQuot' x)).mp
    ((isCM_iff_isCMMod.mp h).quotSMulTop hx (isSMulRegular_of_mem_nonZeroDivisors' reg)))
end IsCM
end ReciprocityTheory.CA
