-- Prove2me | solution 1 for Sherlocking.InfoPolicy.cutoffs_monotone
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:25:09.90227+00:00
-- url     : https://prove2.me/submissions/10b0c889-6f26-4de2-a845-0c55bfa24fc0

import Mathlib
import Definitions.Def_Sherlocking_InfoPolicy_Model

namespace Aux_SH_cut

lemma mono (K : ℝ) (hK : 0 < K) (D : ℝ → ℝ) (hD : Antitone D) :
    Monotone (fun r => if K < D r then K / D r else 1) := by
  intro a b hab
  simp only
  have hDab := hD hab
  split_ifs with h1 h2 h2
  · exact div_le_div_of_nonneg_left hK.le (by linarith) hDab
  · exact (div_le_one (by linarith)).mpr h1.le
  · exfalso; linarith
  · exact le_refl _

lemma smono (K : ℝ) (hK : 0 < K) (D : ℝ → ℝ) (hD : StrictAnti D) (S : Set ℝ)
    (hS : ∀ r ∈ S, K < D r) :
    StrictMonoOn (fun r => if K < D r then K / D r else 1) S := by
  intro a ha b hb hab
  simp only
  rw [if_pos (hS a ha), if_pos (hS b hb)]
  have := hS b hb
  exact div_lt_div_of_pos_left hK (by linarith) (hD hab)

end Aux_SH_cut

open Sherlocking.InfoPolicy in
theorem solution (K δ : ℝ) (hδ1 : δ < 1) (hK1 : 1 - δ < K) (hK2 : K < δ) : MonotoneOn (fun r => thetaP K δ r) (Set.Icc 0 1) ∧ StrictMonoOn (fun r => thetaP K δ r) (Set.Ico 0 (1 - K / δ)) ∧ MonotoneOn (fun r => thetaS K r) (Set.Icc 0 1) ∧ StrictMonoOn (fun r => thetaS K r) (Set.Ico 0 (1 - K)) ∧ (∀ θ : ℝ, 0 < θ → StrictAntiOn (fun r => alpha K δ θ r) (Set.Ico 0 1)) ∧ (∀ r ∈ Set.Ico (0:ℝ) 1, StrictMonoOn (fun θ => alpha K δ θ r) (Set.Ioi 0)) := by
  have hK : 0 < K := by linarith
  have hδ : 0 < δ := by linarith
  have hDP : StrictAnti (fun r : ℝ => δ * (1 - r)) := by
    intro a b hab; simp only; nlinarith
  have hDS : StrictAnti (fun r : ℝ => 1 - r) := by
    intro a b hab; simp only; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Aux_SH_cut.mono K hK (fun r => δ * (1 - r)) hDP.antitone).monotoneOn _
  · apply Aux_SH_cut.smono K hK (fun r => δ * (1 - r)) hDP
    intro r hr
    have h := hr.2
    have : K / δ < 1 - r := by linarith
    rw [div_lt_iff₀ hδ] at this
    linarith
  · exact (Aux_SH_cut.mono K hK (fun r => 1 - r) hDS.antitone).monotoneOn _
  · apply Aux_SH_cut.smono K hK (fun r => 1 - r) hDS
    intro r hr
    have h := hr.2
    linarith
  · intro θ hθ a ha b hb hab
    simp only [alpha]
    have hb1 : 0 < 1 - b := by linarith [hb.2]
    have h1 : K / ((1 - a) * θ) < K / ((1 - b) * θ) :=
      div_lt_div_of_pos_left hK (by positivity) (by nlinarith)
    have h2 : 0 < 1 / δ := by positivity
    nlinarith
  · intro r hr a ha b hb hab
    simp only [alpha]
    simp only [Set.mem_Ioi] at ha hb
    have hr1 : 0 < 1 - r := by linarith [hr.2]
    have h1 : K / ((1 - r) * b) < K / ((1 - r) * a) :=
      div_lt_div_of_pos_left hK (by positivity) (by nlinarith)
    have h2 : 0 < 1 / δ := by positivity
    nlinarith
