-- Prove2me | solution 1 for SpatialDemandEq.Optimal.Supplement.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:11:02.216281+00:00
-- url     : https://prove2.me/submissions/25ddc06d-2203-49ca-a4a8-ba792823a958

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model
import Definitions.Def_SpatialDemandEq_Optimal_Supplement_Model

open SpatialDemandEq
open SpatialDemandEq.Optimal
open SpatialDemandEq.Optimal.Supplement

theorem solution {K : ℕ} (c lam : ℝ) (hc : 0 < c) (hlam : 0 < lam) (μ : Fin K → ℝ)
    (hμ : ∀ k, 0 < μ k) (hcap : lam < ∑ k, μ k) :
    wbar c lam μ < ⊤ := by
      classical
      let δ : ℝ := (∑ k, μ k - lam) / ((K : ℝ) + 1)
      have hδ : 0 < δ := by
        dsimp [δ]
        exact div_pos (sub_pos.mpr hcap) (by positivity)
      have hδeq : δ * ((K : ℝ) + 1) = ∑ k, μ k - lam := by
        dsimp [δ]
        exact div_mul_cancel₀ _ (by positivity)
      have hslack : ∀ a ∈ simplex K, ∃ k, δ ≤ μ k - lam * a k := by
        intro a ha
        have hsum : ∑ k, (μ k - lam * a k) = ∑ k, μ k - lam := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ha.2, mul_one]
        by_contra h
        push_neg at h
        have hb : (∑ k, (μ k - lam * a k)) ≤ ∑ _k : Fin K, δ := by
          exact Finset.sum_le_sum (fun k _ => (h k).le)
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
        rw [hsum] at hb
        nlinarith
      have hbound : wbar c lam μ ≤ ((c / δ : ℝ) : EReal) := by
        unfold wbar
        refine iSup_le fun a => iSup_le fun ha => ?_
        obtain ⟨k, hk⟩ := hslack a ha
        have hstable : lam * a k < μ k := by linarith
        have hquot : c / (μ k - lam * a k) ≤ c / δ :=
          div_le_div_of_nonneg_left hc.le hδ hk
        refine (iInf_le (fun k => waitCost c lam μ k (a k)) k).trans ?_
        simp only [waitCost, if_pos hstable]
        exact_mod_cast hquot
      exact lt_of_le_of_lt hbound (by simp)
