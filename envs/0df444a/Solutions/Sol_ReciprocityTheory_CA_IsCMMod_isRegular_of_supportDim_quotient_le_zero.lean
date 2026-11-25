-- Prove2me | solution 1 for ReciprocityTheory.CA.IsCMMod.isRegular_of_supportDim_quotient_le_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:06:49.264738+00:00
-- url     : https://prove2.me/submissions/70b3f892-b1a6-4598-b9cd-8427ec64a4ca

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularAppendOfModDepthGE
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_AssDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Unmixed
import Theorems.Thm_ReciprocityTheory_CA_IsCMMod_quotSMulTop
import Theorems.Thm_ReciprocityTheory_CA_IsCMMod_isSMulRegular_of_supportDim_quotSMulTop_lt
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
private theorem unm_supportDim_le_quotient_add [IsNoetherianRing R] :
    ∀ (ys : List R) (N : Type*) [AddCommGroup N] [Module R N] [Module.Finite R N],
      (∀ r ∈ ys, r ∈ maximalIdeal R) →
      Module.supportDim R N ≤
        Module.supportDim R (N ⧸ Ideal.ofList ys • (⊤ : Submodule R N)) + ys.length
  | [], N, _, _, _, _ => by
    rw [Ideal.ofList_nil, Submodule.bot_smul,
      Module.supportDim_eq_of_equiv (Submodule.quotEquivOfEqBot ⊥ rfl)]
    simp
  | y :: ys, N, _, _, _, hys => by
    have h1 := Module.supportDim_le_supportDim_quotSMulTop_succ (M := N) (hys y List.mem_cons_self)
    have h2 := unm_supportDim_le_quotient_add ys (QuotSMulTop y N)
      (fun s hs => hys s (List.mem_cons_of_mem y hs))
    rw [Module.supportDim_eq_of_equiv (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner N y ys)]
    calc Module.supportDim R N ≤ Module.supportDim R (QuotSMulTop y N) + 1 := h1
      _ ≤ (Module.supportDim R (QuotSMulTop y N ⧸ Ideal.ofList ys • (⊤ : Submodule R (QuotSMulTop y N)))
            + ys.length) + 1 := by gcongr
      _ = _ := by
        rw [List.length_cons, add_assoc]
        push_cast
        rfl
end ReciprocityTheory.CA
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
namespace ReciprocityTheory.CA
namespace IsCMMod
theorem _root_.solution (h : IsCMMod R M) (xs : List R)
    (hxs : ∀ r ∈ xs, r ∈ maximalIdeal R) (hlen : (xs.length : WithBot ℕ∞) = Module.supportDim R M)
    (h0 : Module.supportDim R (M ⧸ Ideal.ofList xs • (⊤ : Submodule R M)) ≤ 0) :
    IsRegular M xs := by
  induction xs generalizing M with
  | nil =>
    obtain ⟨-, -, n, hdim, hdep⟩ := id h
    have hn : ((0 : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
      rw [← hdim, ← hlen] <;> rfl
    have hn' : n = 0 := by exact_mod_cast hn.symm
    subst hn'
    obtain ⟨rs, hrs, -, hreg⟩ := id hdep
    cases rs with
    | nil => exact hreg
    | cons _ _ => simp at hrs
  | cons x xs ih =>
    obtain ⟨hR, hfin, n, hdim, hdep⟩ := id h
    haveI := hR
    haveI := hfin
    have hx : x ∈ maximalIdeal R := hxs x (by simp)
    have hxs' : ∀ r ∈ xs, r ∈ maximalIdeal R := fun r hr => hxs r (by simp [hr])
    have e := Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x xs
    have hs : Module.support R (M ⧸ Ideal.ofList (x :: xs) • (⊤ : Submodule R M)) =
        Module.support R
          (QuotSMulTop x M ⧸ Ideal.ofList xs • (⊤ : Submodule R (QuotSMulTop x M))) :=
      (Module.support_subset_of_surjective e.symm.toLinearMap e.symm.surjective).antisymm
        (Module.support_subset_of_surjective e.toLinearMap e.surjective)
    have hdd : Module.supportDim R (M ⧸ Ideal.ofList (x :: xs) • (⊤ : Submodule R M)) =
        Module.supportDim R
          (QuotSMulTop x M ⧸ Ideal.ofList xs • (⊤ : Submodule R (QuotSMulTop x M))) := by
      unfold Module.supportDim
      rw [hs]
    have hdQ : Module.supportDim R
        (QuotSMulTop x M ⧸ Ideal.ofList xs • (⊤ : Submodule R (QuotSMulTop x M))) ≤ 0 := by
      rw [← hdd]
      exact h0
    have hQle : Module.supportDim R (QuotSMulTop x M) ≤ (xs.length : WithBot ℕ∞) := by
      have h3 := unm_supportDim_le_quotient_add xs (QuotSMulTop x M) hxs'
      calc Module.supportDim R (QuotSMulTop x M) ≤ _ := h3
        _ ≤ 0 + (xs.length : WithBot ℕ∞) := by
          first | gcongr | exact add_le_add_right hdQ _
        _ = (xs.length : WithBot ℕ∞) := zero_add _
    have hlen' : Module.supportDim R M = (xs.length : WithBot ℕ∞) + 1 := by
      first
      | (rw [← hlen]; simp)
      | (rw [← hlen, List.length_cons, Nat.cast_succ])
      | (rw [← hlen]; push_cast; rfl)
    have hlt : Module.supportDim R (QuotSMulTop x M) < Module.supportDim R M := by
      have hl : ((xs.length : ℕ) : WithBot ℕ∞) < ((xs.length + 1 : ℕ) : WithBot ℕ∞) := by
        exact_mod_cast Nat.lt_succ_self _
      rw [hlen']
      push_cast at hl
      exact lt_of_le_of_lt hQle hl
    have reg : IsSMulRegular M x := h.isSMulRegular_of_supportDim_quotSMulTop_lt hlt
    have hQ : IsCMMod R (QuotSMulTop x M) := h.quotSMulTop hx reg
    have hsd : Module.supportDim R (QuotSMulTop x M) + 1 = Module.supportDim R M := by
      first
      | exact Module.supportDim_quotSMulTop_succ_eq_supportDim reg hx
      | exact Module.supportDim_quotSMulTop_succ_eq_supportDim hx reg
      | exact supportDim_quotSMulTop_succ_eq_supportDim reg hx
    have hlenQ : (xs.length : WithBot ℕ∞) = Module.supportDim R (QuotSMulTop x M) := by
      rw [hlen'] at hsd
      have hsd' : Module.supportDim R (QuotSMulTop x M) + 1 = ((xs.length + 1 : ℕ) : WithBot ℕ∞) := by
        rw [hsd] <;> norm_cast
      obtain ⟨m, hm1, hm2⟩ := unm_add_one_eq hsd'
      have hm : xs.length = m := by omega
      rw [hm2, hm]
    rw [RingTheory.Sequence.isRegular_cons_iff]
    exact ⟨reg, ih hQ hxs' hlenQ hdQ⟩
end IsCMMod
end ReciprocityTheory.CA
