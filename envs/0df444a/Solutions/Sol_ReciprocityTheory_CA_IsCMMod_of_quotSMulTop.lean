-- Prove2me | solution 1 for ReciprocityTheory.CA.IsCMMod.of_quotSMulTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:08:43.095884+00:00
-- url     : https://prove2.me/submissions/97f50d10-57fb-4608-b048-3658b3d8a207

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_AssDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Unmixed
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_of_quotSMulTop


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
namespace ReciprocityTheory.CA
namespace IsCMMod
theorem _root_.solution [IsNoetherianRing R] [Module.Finite R M] {x : R}
    (hx : x ∈ maximalIdeal R) (reg : IsSMulRegular M x) (h : IsCMMod R (QuotSMulTop x M)) :
    IsCMMod R M := by
  obtain ⟨-, -, n, hdim, hdep⟩ := id h
  have hsd : Module.supportDim R (QuotSMulTop x M) + 1 = Module.supportDim R M := by
    first
    | exact Module.supportDim_quotSMulTop_succ_eq_supportDim reg hx
    | exact Module.supportDim_quotSMulTop_succ_eq_supportDim hx reg
    | exact supportDim_quotSMulTop_succ_eq_supportDim reg hx
  unfold IsCMMod
  refine ⟨inferInstance, inferInstance, n + 1, ?_, hdep.of_quotSMulTop hx reg⟩
  first
  | (rw [← hsd, hdim]; done)
  | (rw [← hsd, hdim]; norm_cast)
  | (rw [← hsd, hdim]; simp)
end IsCMMod
end ReciprocityTheory.CA
