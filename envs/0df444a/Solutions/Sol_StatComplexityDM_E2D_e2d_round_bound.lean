-- Prove2me | solution 1 for StatComplexityDM.E2D.e2d_round_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:34:47.342006+00:00
-- url     : https://prove2.me/submissions/5ef7c9b1-2e9e-4c56-b287-94cb997db6ba

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_FoundationsRL_GeneralDM_DEC
import Definitions.Def_StatComplexityDM_LowerBound_Core

open FoundationsRL.GeneralDM

theorem solution {S Y : Type*} [Fintype S] [Fintype Y]
    (rew : Y → ℝ) (hrew : ∀ y, 0 ≤ rew y ∧ rew y ≤ 1)
    (piStar : (S → Y → ℝ) → S) (γ : ℝ) (hγ : 0 < γ)
    (C : Set (S → Y → ℝ)) (hC : ∀ m ∈ C, StatComplexityDM.LowerBound.IsModel m)
    (Mstar : S → Y → ℝ) (hMstar : Mstar ∈ C) (mhat : S → Y → ℝ)
    (p : S → ℝ) (hp : StatComplexityDM.LowerBound.IsDist p)
    (hpmin : sSup ((fun m : S → Y → ℝ =>
        ∑ π, p π * (fM rew m (piStar m) - fM rew m π - γ * hellingerSq (m π) (mhat π))) '' C)
      = decGf C rew piStar γ mhat) :
    ∑ π, p π * (fM rew Mstar (piStar Mstar) - fM rew Mstar π)
        - γ * ∑ π, p π * hellingerSq (Mstar π) (mhat π)
      ≤ decGf C rew piStar γ mhat := by
  have hfM : ∀ m ∈ C, ∀ π, 0 ≤ fM rew m π ∧ fM rew m π ≤ 1 := by
    intro m hm π
    obtain ⟨h0, h1⟩ := hC m hm π
    unfold fM
    constructor
    · exact Finset.sum_nonneg (fun y _ => mul_nonneg (h0 y) (hrew y).1)
    · calc ∑ y, m π y * rew y ≤ ∑ y, m π y :=
            Finset.sum_le_sum (fun y _ => mul_le_of_le_one_right (h0 y) (hrew y).2)
        _ = 1 := h1
  have hH : ∀ a b : Y → ℝ, 0 ≤ hellingerSq a b := fun a b =>
    Finset.sum_nonneg (fun y _ => sq_nonneg _)
  rw [← hpmin]
  have e : ∑ π, p π * (fM rew Mstar (piStar Mstar) - fM rew Mstar π)
        - γ * ∑ π, p π * hellingerSq (Mstar π) (mhat π)
      = ∑ π, p π * (fM rew Mstar (piStar Mstar) - fM rew Mstar π - γ * hellingerSq (Mstar π) (mhat π)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun π _ => ?_)
    ring
  rw [e]
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro _ ⟨m, hm, rfl⟩
    calc ∑ π, p π * (fM rew m (piStar m) - fM rew m π - γ * hellingerSq (m π) (mhat π))
        ≤ ∑ π, p π * 1 := by
          refine Finset.sum_le_sum (fun π _ => mul_le_mul_of_nonneg_left ?_ (hp.1 π))
          have h1 := (hfM m hm (piStar m)).2
          have h2 := (hfM m hm π).1
          have h3 := hH (m π) (mhat π)
          nlinarith
      _ = 1 := by simp [hp.2]
  · exact ⟨Mstar, hMstar, rfl⟩
