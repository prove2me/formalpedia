-- Prove2me | solution 1 for ReciprocityTheory.CA.ModDepthGE.of_quotSMulTop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:05:58.758817+00:00
-- url     : https://prove2.me/submissions/9833bc8f-b3c7-48bd-9a78-919c9ef22396

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_Lemmata_GeneralBFactSide_Imports
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence Pointwise
variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
namespace ReciprocityTheory.CA
namespace ModDepthGE
theorem _root_.solution {x : R} (hx : x ∈ maximalIdeal R) (reg : IsSMulRegular M x)
    {n : ℕ} (h : ModDepthGE R (QuotSMulTop x M) n) : ModDepthGE R M (n + 1) := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := h
  refine ⟨x :: rs, by simp [hlen], ?_, (isRegular_cons_iff M x rs).mpr ⟨reg, hreg⟩⟩
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hx
  · exact hmem r hr
end ModDepthGE
end ReciprocityTheory.CA
