-- Prove2me | solution 1 for StableVotingDistortion.W_nonneg_monotone
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T12:00:16.333203+00:00
-- url     : https://prove2.me/submissions/2f6bbab2-cfe5-4ac2-8e15-4ef7119f0a49

import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_IsGStable
import Definitions.Def_StableVotingDistortion_IsScoreFunction
import Definitions.Def_StableVotingDistortion_offset
import Definitions.Def_StableVotingDistortion_scorePrimitives
import Definitions.Def_StableVotingDistortion_slices
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

-- Source module VerifierPotential
section
set_option autoImplicit true
namespace StableVotingDistortion
open Set PctDistortion

theorem W_nonneg_monotone {lam : ℝ} {ϕ : ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ)
    (hadd : AntitoneOn (fun r => ϕ r + r) (Set.Icc lam 1)) :
    (∀ x ∈ Set.Ico 0 lam, (∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ Wx lam ϕ x z) ∧
        MonotoneOn (Wx lam ϕ x) (Set.Icc 0 1)) ∧
      ∀ {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C) (D : C → ℝ), D ∈ stdSimplex ℝ C → ∀ aStar : C,
        0 < Aval lam ϕ E D aStar →
          (∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ WAvg lam ϕ E D aStar z) ∧
            MonotoneOn (WAvg lam ϕ E D aStar) (Set.Icc 0 1) := by
  have hz := (gPhi_properties hϕ).1
  have hl := hϕ.lam_mem
  have each (x : ℝ) (hx : x ∈ Ico 0 lam) :
      (∀ z ∈ Icc (0:ℝ) 1, 0 ≤ Wx lam ϕ x z) ∧ MonotoneOn (Wx lam ϕ x) (Icc 0 1) := by
    have hp := hϕ.pos x hx
    let R := (lam-x)/ϕ x
    have hR : 1 ≤ R := (one_le_div hp).mpr (hϕ.le_lam_sub x ⟨hx.1,hx.2.le.trans hl.2.le⟩)
    have hh {a b : ℝ} (ha : a ∈ Icc lam 1) (hb : b ∈ Icc lam 1) (hab : a≤b) :
        lam-a-R*ϕ a ≤ lam-b-R*ϕ b := by
      have hg := hadd ha hb hab
      dsimp at hg
      have hd : 0≤ϕ a-ϕ b := by linarith
      have hprod := mul_nonneg (sub_nonneg.mpr hR) hd
      nlinarith
    have upper (z : ℝ) (hz' : z∈Icc lam 1) : 0 ≤ lam-z-R*ϕ z := by
      have h := hh (show lam ∈ Icc lam 1 from ⟨le_rfl,hl.2.le⟩) hz' hz'.1
      simpa [hz] using h
    refine ⟨fun z h => ?_,fun a ha b hb hab => ?_⟩
    · unfold Wx
      split_ifs with le
      · exact le_rfl
      · exact upper z ⟨le_of_not_ge le,h.2⟩
    · by_cases hbL : b ≤ lam
      · simp [Wx,hbL,hab.trans hbL]
      · by_cases haL : a ≤ lam
        · simp only [Wx, if_pos haL,if_neg hbL]
          exact upper b ⟨le_of_not_ge hbL,hb.2⟩
        · simp only [Wx, if_neg haL,if_neg hbL]
          exact hh ⟨le_of_not_ge haL,ha.2⟩ ⟨le_of_not_ge hbL,hb.2⟩ hab
  refine ⟨each,?_⟩
  intro V C _ _ _ _ E D hD a hA
  have hnon (v : V) : 0 ≤ sv E D a v := Finset.sum_nonneg (fun b _ => hD.1 b)
  constructor
  · intro z hz
    apply div_nonneg _ hA.le
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro v _
    split_ifs with Hv
    · exact mul_nonneg (hϕ.pos _ ⟨hnon v,Hv⟩).le ((each _ ⟨hnon v,Hv⟩).1 _ hz)
    · exact le_rfl
  · intro y hy z hz hyz
    apply div_le_div_of_nonneg_right _ hA.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro v _
    split_ifs with Hv
    · exact mul_le_mul_of_nonneg_left ((each _ ⟨hnon v,Hv⟩).2 hy hz hyz) (hϕ.pos _ ⟨hnon v,Hv⟩).le
    · exact le_rfl

end StableVotingDistortion
end

open PctDistortion
open StableVotingDistortion

theorem solution :
    ∀ {lam : ℝ} {ϕ : ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ)
    (hadd : AntitoneOn (fun r => ϕ r + r) (Set.Icc lam 1)),
    (∀ x ∈ Set.Ico 0 lam, (∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ Wx lam ϕ x z) ∧
        MonotoneOn (Wx lam ϕ x) (Set.Icc 0 1)) ∧
      ∀ {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C) (D : C → ℝ), D ∈ stdSimplex ℝ C → ∀ aStar : C,
        0 < Aval lam ϕ E D aStar →
          (∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ WAvg lam ϕ E D aStar z) ∧
            MonotoneOn (WAvg lam ϕ E D aStar) (Set.Icc 0 1) :=
  @StableVotingDistortion.W_nonneg_monotone
