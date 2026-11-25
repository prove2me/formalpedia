-- Prove2me | solution 1 for ReciprocityTheory.CA.IsCMMod.quotSMulTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:00:15.981934+00:00
-- url     : https://prove2.me/submissions/bb431a82-a271-4de1-a16a-3ff84564ac5f

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_AssDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Unmixed
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_quotSMulTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
private theorem unm_add_one_eq {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 = n) :
    ∃ m : ℕ, n = m + 1 ∧ a = m := by
  induction a using WithBot.recBotCoe with
  | bot =>
    exfalso
    first
    | (simp at h; done)
    | (rw [WithBot.bot_add] at h; exact WithBot.bot_ne_coe (a := (n : ℕ∞)) (by exact_mod_cast h))
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : (⊤ : ℕ∞) + 1 = (n : ℕ∞) := by exact_mod_cast h
      simp at h'
    | coe k =>
      have h' : k + 1 = n := by exact_mod_cast h
      exact ⟨k, h'.symm, by first | rfl | norm_cast | simp⟩
end ReciprocityTheory.CA
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
namespace ReciprocityTheory.CA
namespace IsCMMod
theorem _root_.solution (h : IsCMMod R M) {x : R} (hx : x ∈ maximalIdeal R)
    (reg : IsSMulRegular M x) : IsCMMod R (QuotSMulTop x M) := by
  obtain ⟨hR, hfin, n, hdim, hdep⟩ := id h
  haveI := hR
  haveI := hfin
  have hsd : Module.supportDim R (QuotSMulTop x M) + 1 = Module.supportDim R M := by
    first
    | exact Module.supportDim_quotSMulTop_succ_eq_supportDim reg hx
    | exact Module.supportDim_quotSMulTop_succ_eq_supportDim hx reg
    | exact supportDim_quotSMulTop_succ_eq_supportDim reg hx
  rw [hdim] at hsd
  obtain ⟨m, rfl, hm⟩ := unm_add_one_eq hsd
  unfold IsCMMod
  exact ⟨hR, by first | infer_instance | exact Module.Finite.quotient R _, m, hm,
    hdep.quotSMulTop hx reg⟩
end IsCMMod
end ReciprocityTheory.CA
