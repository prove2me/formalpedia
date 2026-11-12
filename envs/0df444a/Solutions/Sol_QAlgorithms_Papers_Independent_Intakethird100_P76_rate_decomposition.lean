-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P76.rate_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T20:06:31.275924+00:00
-- url     : https://prove2.me/submissions/5acee8c5-ee3e-4f15-b6ad-3743f0127bec

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P76

open scoped BigOperators

open Filter Set

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

namespace Aux_RD76

open QAlgorithms.Papers.Independent.Intakethird100.P76

theorem relabel {O A B : Type*} [Fintype O] (p : O → ℝ) (f : O → A) (g : O → B)
    (h : ∀ t o, f t = f o ↔ g t = g o) :
    observationEntropyBits p f = observationEntropyBits p g := by
  unfold observationEntropyBits
  congr 1
  apply Finset.sum_congr rfl
  intro o _
  congr 2
  apply Finset.sum_congr rfl
  intro t _
  by_cases hft : f t = f o
  · rw [if_pos hft, if_pos ((h t o).mp hft)]
  · rw [if_neg hft, if_neg (fun hg => hft ((h t o).mpr hg))]

end Aux_RD76

variable {S X Y Z : Type} [Fintype S] [Fintype X] [Fintype Y] [Fintype Z]
  [Nonempty S] [Nonempty X] [Nonempty Y] [Nonempty Z]

variable {n u w : ℕ}

open QAlgorithms.Papers.Independent.Intakethird100.P76 in
theorem solution (W : DMBC S X Y Z) (p : S → ℝ) (hp : IsLaw p) :
    advantage W p = channelRate W p + residualSourceRate W p := by
  have r1 := Aux_RD76.relabel (excitationJointMass W p)
    (fun o => ((obsX o, obsS o), obsY o)) (fun o => (obsX o, (obsY o, obsS o)))
    (fun t o => by simp only [Prod.mk.injEq]; tauto)
  have r2 := Aux_RD76.relabel (excitationJointMass W p)
    (fun o => ((obsX o, obsS o), obsZ o)) (fun o => (obsX o, (obsZ o, obsS o)))
    (fun t o => by simp only [Prod.mk.injEq]; tauto)
  have r3 := Aux_RD76.relabel (excitationJointMass W p)
    (fun o => (obsS o, obsY o)) (fun o => (obsY o, obsS o))
    (fun t o => by simp only [Prod.mk.injEq]; tauto)
  have r4 := Aux_RD76.relabel (excitationJointMass W p)
    (fun o => (obsS o, obsZ o)) (fun o => (obsZ o, obsS o))
    (fun t o => by simp only [Prod.mk.injEq]; tauto)
  simp only [advantage, channelRate, residualSourceRate, observationMutualInfoBits, condInfo,
    condEntropy]
  linarith [r1, r2, r3, r4]
