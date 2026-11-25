-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.SliceClasses.C_nil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:38:39.764898+00:00
-- url     : https://prove2.me/submissions/1237dc49-c452-43dc-b61d-6efd5fbe2c51

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_SliceTensors_PSliceC
import Theorems.Thm_PositivityTheory_Rg_Rs_SliceClasses_C_pow_mem
import Theorems.Thm_PositivityTheory_Rg_Rs_SliceClasses_C_sub_one_mem
import Theorems.Thm_PositivityTheory_Rg_Rs_SliceClasses_C_comm_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.SliceClasses
variable {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] {ι : Type*}
namespace PositivityTheory.Rg.Rs.SliceClasses
theorem _root_.solution (M : ι → Module.End ℂ U) (hc : ∀ i j, Commute (M i) (M j)) :
    ∀ (n : ℕ) (P : Submodule ℂ U), Module.finrank ℂ P = n → P ≠ ⊥ → (∀ i, ∀ v ∈ P, M i v ∈ P) →
      (∀ i, ∀ v ∈ P, ∃ k : ℕ, ((M i - 1) ^ k) v = 0) → ∃ w ∈ P, w ≠ 0 ∧ ∀ i, M i w = w := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hn hP hst hnil
  by_cases hall : ∀ i, ∀ v ∈ P, M i v = v
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    exact ⟨v, hv, hv0, fun i => hall i v hv⟩
  push Not at hall
  obtain ⟨i, v, hv, hMv⟩ := hall
  classical
  set P' : Submodule ℂ U := P ⊓ LinearMap.ker (M i - 1) with hP'def
  have hlt : P' < P := by
    refine lt_of_le_of_ne inf_le_left fun h => hMv ?_
    have h2 : v ∈ P' := h ▸ hv
    have h3 := (Submodule.mem_inf.1 h2).2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h3
    exact h3
  have hne : P' ≠ ⊥ := by
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    have hex : ∃ k, (((M i - 1) ^ k : Module.End ℂ U)) u = 0 := hnil i u hu
    have hkk : ((M i - 1) ^ Nat.find hex) u = 0 := Nat.find_spec hex
    have hkk0 : Nat.find hex ≠ 0 := by
      intro h0; rw [h0, pow_zero, Module.End.one_apply] at hkk; exact hu0 hkk
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hkk0
    have hmin : ((M i - 1) ^ j) u ≠ 0 := Nat.find_min hex (by omega)
    refine (Submodule.ne_bot_iff _).2 ⟨((M i - 1) ^ j) u, Submodule.mem_inf.2 ⟨?_, ?_⟩, hmin⟩
    · exact C_pow_mem (C_sub_one_mem (hst i)) j u hu
    · rw [LinearMap.mem_ker, ← Module.End.mul_apply, ← pow_succ', show j + 1 = Nat.find hex by omega]; exact hkk
  have hst' : ∀ l, ∀ x ∈ P', M l x ∈ P' := by
    intro l x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    refine Submodule.mem_inf.2 ⟨hst l x hx1, ?_⟩
    rw [LinearMap.mem_ker] at hx2 ⊢
    have := C_comm_pow hc i l 1 x
    rw [pow_one] at this
    rw [← this, hx2, map_zero]
  have hnil' : ∀ l, ∀ x ∈ P', ∃ k : ℕ, ((M l - 1) ^ k) x = 0 := fun l x hx =>
    hnil l x (Submodule.mem_inf.1 hx).1
  obtain ⟨w, hw, hw0, hfix⟩ := ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) P' rfl hne hst' hnil'
  exact ⟨w, (Submodule.mem_inf.1 hw).1, hw0, hfix⟩
end PositivityTheory.Rg.Rs.SliceClasses
