-- Prove2me | solution 1 for ReviewInfoShare.eq_6_first_stage_prices
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:28:55.092423+00:00
-- url     : https://prove2.me/submissions/f656e1a1-87a9-43ce-abc9-475b178800e5

import Mathlib
import Definitions.Def_ReviewInfoShare_Model
import Definitions.Def_ReviewInfoShare_Wholesale

namespace Aux_RIS6

lemma pmax_exists (D w K : ℝ) :
    IsMaxOn (fun p => (p - w) * (D - p) + K) Set.univ ((D + w) / 2) := by
  rw [isMaxOn_iff]; intro p _
  nlinarith [sq_nonneg (p - (D + w) / 2)]

lemma pmax_exists0 (D w : ℝ) :
    IsMaxOn (fun p => (p - w) * (D - p)) Set.univ ((D + w) / 2) := by
  rw [isMaxOn_iff]; intro p _
  nlinarith [sq_nonneg (p - (D + w) / 2)]

lemma pmax_unique (D w K x : ℝ) (h : IsMaxOn (fun p => (p - w) * (D - p) + K) Set.univ x) :
    x = (D + w) / 2 := by
  have := isMaxOn_iff.mp h ((D + w) / 2) (Set.mem_univ _)
  nlinarith [sq_nonneg (x - (D + w) / 2)]

lemma wmax_exists (D c K : ℝ) :
    IsMaxOn (fun w => (w - c) * (D - (D + w) / 2) + K) Set.univ ((D + c) / 2) := by
  rw [isMaxOn_iff]; intro p _
  nlinarith [sq_nonneg (p - (D + c) / 2)]

lemma wmax_exists0 (D c : ℝ) :
    IsMaxOn (fun w => (w - c) * (D - (D + w) / 2)) Set.univ ((D + c) / 2) := by
  rw [isMaxOn_iff]; intro p _
  nlinarith [sq_nonneg (p - (D + c) / 2)]

end Aux_RIS6

open ReviewInfoShare in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Params) (hP : P.Admissible)
    (S : Signals Ω) (hS : IsSignalModel P S) (r : Regime) (i : Info) (q : Quality) :
    (∃ σ, IsWholesaleEq P S r i q σ) ∧
    ∀ σ, IsWholesaleEq P S r i q σ →
      σ.p₁ σ.w₁ = (3 * P.α + 3 * P.μ * P.qual q + P.cost q) / 4 ∧
      σ.w₁ = (P.α + P.μ * P.qual q + P.cost q) / 2 := by
  refine ⟨?_, ?_⟩
  · refine ⟨⟨fun w t z => (P.α + t * z + w) / 2, fun t z => (P.α + t * z + P.cost q) / 2,
      fun w => (P.α + P.μ * P.qual q + w) / 2, (P.α + P.μ * P.qual q + P.cost q) / 2⟩, ?_⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro w t z
      exact Aux_RIS6.pmax_exists0 _ _
    · intro t z
      exact Aux_RIS6.wmax_exists0 _ _
    · intro w
      exact Aux_RIS6.pmax_exists _ _ _
    · exact Aux_RIS6.wmax_exists _ _ _
  · intro σ h
    have hp1 : ∀ w, σ.p₁ w = (P.α + P.μ * P.qual q + w) / 2 := fun w =>
      Aux_RIS6.pmax_unique _ _ _ _ (h.2.1 w)
    have h22 := isMaxOn_iff.mp h.2.2 ((P.α + P.μ * P.qual q + P.cost q) / 2) (Set.mem_univ _)
    rw [hp1, hp1] at h22
    have hw : σ.w₁ = (P.α + P.μ * P.qual q + P.cost q) / 2 := by
      nlinarith [sq_nonneg (σ.w₁ - (P.α + P.μ * P.qual q + P.cost q) / 2)]
    refine ⟨?_, hw⟩
    rw [hp1, hw]; ring
