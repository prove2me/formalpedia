-- Prove2me | solution 1 for StableVotingDistortion.gPhi_properties
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T12:00:20.057167+00:00
-- url     : https://prove2.me/submissions/cbba088b-86cb-4e99-9aa6-fd3e04d85b56

import Definitions.Def_StableVotingDistortion_IsGStable
import Definitions.Def_StableVotingDistortion_IsScoreFunction
import Definitions.Def_StableVotingDistortion_scorePrimitives
import Mathlib

-- Source module ScoreProperties
section
set_option autoImplicit true
namespace StableVotingDistortion
open Set MeasureTheory

theorem gPhi_properties {lam : ℝ} {ϕ : ℝ → ℝ} (h : IsScoreFunction lam ϕ) :
    ϕ lam = 0 ∧ (∀ r ∈ Set.Icc lam 1, ϕ r ≤ 0) ∧ IsActivation (gPhi ϕ) ∧
      gPhi ϕ 0 = 0 ∧ gPhi ϕ 1 = 1 ∧
      ∀ r ∈ Set.Icc (0 : ℝ) 1, ϕ r = (1 + ϕ 0) * ((∫ u in (0 : ℝ)..1, gPhi ϕ u) - gPhi ϕ r) := by
  have hl : lam ∈ Icc 0 1 := ⟨h.lam_mem.1.le,h.lam_mem.2.le⟩
  have h0 : 0 < ϕ 0 := h.pos 0 ⟨le_rfl,h.lam_mem.1⟩
  have hd : 0 < 1+ϕ 0 := by linarith
  have hpt : MapsTo ϕ (Ico 0 lam) (Ici 0) := fun x hx => (h.pos x hx).le
  have hc : ContinuousOn ϕ (closure (Ico 0 lam)) := by
    rw [closure_Ico h.lam_mem.1.ne]
    exact h.continuousOn.mono (Icc_subset_Icc le_rfl hl.2)
  have hclosed := hpt.closure_of_continuousOn hc
  rw [closure_Ico h.lam_mem.1.ne, isClosed_Ici.closure_eq] at hclosed
  have hz : ϕ lam = 0 := le_antisymm (by linarith [h.le_lam_sub lam hl]) (hclosed ⟨hl.1,le_rfl⟩)
  have hm : MonotoneOn (gPhi ϕ) (Icc 0 1) := by
    intro x hx y hy hxy
    apply div_le_div_of_nonneg_right _ hd.le
    linarith [h.antitoneOn hx hy hxy]
  have hz0 : gPhi ϕ 0=0 := by simp [gPhi]
  have hz1 : gPhi ϕ 1=1 := by
    rw [gPhi,h.at_one,sub_neg_eq_add,add_comm (ϕ 0) 1,div_self hd.ne']
  have hi := h.continuousOn.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0:ℝ)≤1)
  have hmean : (∫ u in (0:ℝ)..1, gPhi ϕ u) = ϕ 0/(1+ϕ 0) := by
    simp only [gPhi]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (f := fun _ => ϕ 0)
      (g := ϕ) intervalIntegrable_const hi, h.integral_eq_zero, intervalIntegral.integral_const]
    simp
  refine ⟨hz,fun r hr => ?_, ⟨?_,hm,?_⟩,hz0,hz1,fun r _ => ?_⟩
  · rw [← hz]; exact h.antitoneOn hl ⟨hl.1.trans hr.1,hr.2⟩ hr.1
  · exact (continuousOn_const.sub h.continuousOn).div_const _
  · intro z hz
    exact ⟨hz0 ▸ hm (by norm_num) hz hz.1,hz1 ▸ hm hz (by norm_num) hz.2⟩
  · rw [hmean,gPhi]
    field_simp [hd.ne'] <;> ring

end StableVotingDistortion
end


open StableVotingDistortion

theorem solution :
    ∀ {lam : ℝ} {ϕ : ℝ → ℝ} (h : IsScoreFunction lam ϕ),
    ϕ lam = 0 ∧ (∀ r ∈ Set.Icc lam 1, ϕ r ≤ 0) ∧ IsActivation (gPhi ϕ) ∧
      gPhi ϕ 0 = 0 ∧ gPhi ϕ 1 = 1 ∧
      ∀ r ∈ Set.Icc (0 : ℝ) 1, ϕ r = (1 + ϕ 0) * ((∫ u in (0 : ℝ)..1, gPhi ϕ u) - gPhi ϕ r) :=
  @StableVotingDistortion.gPhi_properties
