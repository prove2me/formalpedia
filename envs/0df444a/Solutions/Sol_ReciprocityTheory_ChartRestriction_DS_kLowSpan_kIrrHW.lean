-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.kLowSpan_kIrrHW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:54:13.333252+00:00
-- url     : https://prove2.me/submissions/4c396e5c-f937-461e-b1d8-b90687f771a8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_self_mem_kLowSpan
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kLowSpan_kStable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kLowSpan_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kLowSpan_line

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) (hU : IsInfUnitary ε E) {μ : Fin n → ℝ} {y : M}
    (hy : IsKHWVec ε E μ y) (hy0 : y ≠ 0) (hfin : FiniteDimensional ℂ (kLowSpan ε E y)) :
    IsKIrrHW ε E μ (kLowSpan ε E y) := by
  have hy' : (∀ a, E a a y = (μ a : ℂ) • y) ∧ ∀ a b, a < b → ε a = ε b → E a b y = 0 := hy
  refine ⟨hfin, kLowSpan_kStable hE hy, ?_, y, self_mem_kLowSpan y, hy0, hy⟩
  intro S' hS'le hS'st
  haveI : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'le
  have hperp : IsKStableSub ε E S'ᗮ := by
    intro a b hab v hv
    rw [Submodule.mem_orthogonal]
    intro u hu
    have h := hU b a u v
    have hs : adjSign ε b a = 1 := by simp [adjSign, hab]
    rw [hs, one_mul] at h
    rw [← h]
    exact (Submodule.mem_orthogonal _ _).mp hv _ (hS'st b a hab.symm u hu)
  have hzero : ∀ x, x ∈ S' → x ∈ S'ᗮ → x = 0 := fun x h1 h2 =>
    inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal h1 h2)
  obtain ⟨y1, hy1, y2, hy2, hsum⟩ := S'.exists_add_mem_mem_orthogonal y
  have hy1w : ∀ a, E a a y1 = (μ a : ℂ) • y1 := by
    intro a
    have h := hy'.1 a
    rw [hsum, map_add, smul_add] at h
    have hm : E a a y1 - (μ a : ℂ) • y1 = (μ a : ℂ) • y2 - E a a y2 := by
      rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
    have h0 := hzero _ (sub_mem (hS'st a a rfl y1 hy1) (Submodule.smul_mem _ _ hy1))
      (by rw [hm]; exact sub_mem (Submodule.smul_mem _ _ hy2) (hperp a a rfl y2 hy2))
    exact sub_eq_zero.mp h0
  obtain ⟨c, hc⟩ := kLowSpan_line hE hU hy hy0 (hS'le hy1) hy1w
  by_cases hc0 : c = 0
  · left
    rw [hc0, zero_smul] at hc
    have hyperp : y ∈ S'ᗮ := by rw [hsum, hc, zero_add]; exact hy2
    have hle2 : kLowSpan ε E y ≤ S'ᗮ := kLowSpan_le hperp hyperp
    rw [Submodule.eq_bot_iff]
    intro x hx
    exact hzero x hx (hle2 (hS'le hx))
  · right
    have hyS : y ∈ S' := by
      have hyc : y = c⁻¹ • y1 := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [hyc]
      exact Submodule.smul_mem _ _ hy1
    exact le_antisymm hS'le (kLowSpan_le hS'st hyS)
end ReciprocityTheory.ChartRestriction.DS
