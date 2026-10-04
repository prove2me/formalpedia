-- Prove2me | solution 1 for StarShapedRisk.LawInvariant.robustified_functional_normalized
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T03:17:54.084604+00:00
-- url     : https://prove2.me/submissions/0736f5eb-d918-4804-805b-79db8ba0f479

import Mathlib

set_option autoImplicit false

theorem solution {E : Type*}
    (ψ : Set.Ioo (0 : ℝ) 1 → E → ℝ)
    (G : Set (Set.Ioo (0 : ℝ) 1 → ℝ))
    (hne : G.Nonempty) (hstar : StarConvex ℝ 0 G)
    (hg0 : ∀ g ∈ G, ⨅ α : Set.Ioo (0 : ℝ) 1, (g α : EReal) ≤ 0)
    (e0 : E)
    (hψ0 : ∀ α, ψ α e0 = 0) :
    (⨅ g ∈ G, ⨆ α : Set.Ioo (0 : ℝ) 1, (((ψ α e0 - g α : ℝ)) : EReal)) = 0 := by
  have : Nonempty (Set.Ioo (0 : ℝ) 1) :=
    ⟨⟨1 / 2, by norm_num, by norm_num⟩⟩
  obtain ⟨y, hy⟩ := hne
  have h0G : (0 : Set.Ioo (0 : ℝ) 1 → ℝ) ∈ G := by
    have := hstar hy (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 0 by norm_num)
      (by norm_num)
    simpa using this
  apply le_antisymm
  · refine le_trans (iInf₂_le (0 : Set.Ioo (0 : ℝ) 1 → ℝ) h0G) ?_
    simp [hψ0]
  · refine le_iInf₂ (fun g hg => ?_)
    set S : EReal := ⨆ α : Set.Ioo (0 : ℝ) 1, (((ψ α e0 - g α : ℝ)) : EReal) with hS
    have h1 : -S ≤ ⨅ α : Set.Ioo (0 : ℝ) 1, (g α : EReal) := by
      refine le_iInf (fun α => ?_)
      rw [EReal.neg_le]
      have : (((ψ α e0 - g α : ℝ)) : EReal) ≤ S :=
        le_iSup (fun α : Set.Ioo (0 : ℝ) 1 => (((ψ α e0 - g α : ℝ)) : EReal)) α
      rw [hψ0 α, zero_sub, EReal.coe_neg] at this
      exact this
    have h2 : -S ≤ 0 := le_trans h1 (hg0 g hg)
    have h3 : -(0 : EReal) ≤ S := EReal.neg_le.mp h2
    simpa using h3
