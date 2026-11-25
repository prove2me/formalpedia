-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.le_of_resK_le_of_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:17:21.920111+00:00
-- url     : https://prove2.me/submissions/1f744123-c4f9-46f6-aea1-3821706c6ed3

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_closest
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_mem_resK_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_Obar_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_resK_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_residue_eq_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution {M L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hM : FiniteDimensional ℚ_[p] M) (hML : M ≤ L) (hres : resK p L ≤ resK p M)
    (h : ∀ x ∈ L, ∃ y ∈ M, ‖x‖ = ‖y‖) : L ≤ M := by
  intro x hx
  obtain ⟨m0, hm0, hmin⟩ := exists_closest p hM x
  by_contra hxM
  have hy0 : x - m0 ≠ 0 := fun h0 => hxM (by rw [sub_eq_zero.1 h0]; exact hm0)
  have hyL : x - m0 ∈ L := L.sub_mem hx (hML hm0)
  obtain ⟨k, hk, hyk⟩ := h _ hyL
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [norm_zero, norm_eq_zero] at hyk
    exact hy0 hyk
  have hkn : 0 < ‖k‖ := norm_pos_iff.2 hk0
  have h1 : ‖(x - m0) / k‖ = 1 := by rw [norm_div, hyk, div_self hkn.ne']
  have hmem : IsLocalRing.residue (Obar p) ⟨(x - m0) / k, mem_Obar_iff.2 h1.le⟩ ∈ resK p L :=
    (mem_resK_iff p L _).2 ⟨_, L.div_mem hyL (hML hk), rfl⟩
  obtain ⟨z, hz, hzr⟩ := (mem_resK_iff p M _).1 (hres hmem)
  rw [residue_eq_iff] at hzr
  have hzr' : ‖(z : PadicAlgCl p) - (x - m0) / k‖ < 1 := hzr
  have hlt : ‖x - (m0 + k * (z : PadicAlgCl p))‖ < ‖x - m0‖ := by
    have e : x - (m0 + k * (z : PadicAlgCl p)) = -(k * ((z : PadicAlgCl p) - (x - m0) / k)) := by
      rw [mul_sub, mul_div_cancel₀ _ hk0]
      ring
    rw [e, norm_neg, norm_mul, hyk]
    calc ‖k‖ * ‖(z : PadicAlgCl p) - (x - m0) / k‖ < ‖k‖ * 1 :=
          mul_lt_mul_of_pos_left hzr' hkn
      _ = ‖k‖ := mul_one _
  exact absurd hlt (not_lt.2 (hmin _ (M.add_mem hm0 (M.mul_mem hk hz))))
end ReciprocityTheory.DiscreteGroups.LocalClassField
