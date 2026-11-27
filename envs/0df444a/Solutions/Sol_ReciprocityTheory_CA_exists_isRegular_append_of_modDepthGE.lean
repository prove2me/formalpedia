-- Prove2me | solution 1 for ReciprocityTheory.CA.exists_isRegular_append_of_modDepthGE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:22:46.64507+00:00
-- url     : https://prove2.me/submissions/75ebb954-ea8d-4e50-9814-8fc4b73eeb0d

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_Lemmata_GeneralBFactSide_Imports
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_quotSMulTop

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
variable [IsNoetherianRing R] [Module.Finite R M]
namespace ReciprocityTheory.CA
theorem _root_.solution {rs : List R} (hrs : ∀ r ∈ rs, r ∈ maximalIdeal R)
    (reg : IsRegular M rs) {n : ℕ} (h : ModDepthGE R M (rs.length + n)) :
    ∃ rs' : List R, rs'.length = n ∧ (∀ r ∈ rs', r ∈ maximalIdeal R) ∧
      IsRegular M (rs ++ rs') := by
  induction rs generalizing M with
  | nil =>
    simp only [List.length_nil, zero_add] at h
    obtain ⟨rs', hl, hm, hr⟩ := h
    exact ⟨rs', hl, hm, hr⟩
  | cons r rs ih =>
    have hr : r ∈ maximalIdeal R := hrs r (by simp)
    obtain ⟨rreg, hq⟩ := (isRegular_cons_iff M r rs).mp reg
    have hlen : (r :: rs).length + n = rs.length + n + 1 := by simp; omega
    rw [hlen] at h
    obtain ⟨rs', hl, hm, hreg'⟩ := ih (M := QuotSMulTop r M)
      (fun s hs => hrs s (List.mem_cons_of_mem _ hs)) hq (ModDepthGE.quotSMulTop hr rreg h)
    exact ⟨rs', hl, hm, (isRegular_cons_iff M r _).mpr ⟨rreg, hreg'⟩⟩
end ReciprocityTheory.CA
