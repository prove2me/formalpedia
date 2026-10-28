-- Prove2me | solution 2 for PosetSecretary.LowerBound.proposition_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T07:10:49.735788+00:00
-- url     : https://prove2.me/submissions/605b514c-7c2d-4299-b92e-59642c9ed9b4

import Mathlib
import Definitions.Def_AppliedComb_Posets_width
import Definitions.Def_PosetSecretary_LowerBound_Setting
import Theorems.Thm_PosetSecretary_LowerBound_exists_perturbation_expectedScore_le

-- carved verbatim out of submission 13256a71-f1c4-443e-9f34-4b27aeafa5a5, lines 427-439

section
set_option autoImplicit false
open PosetSecretary.LowerBound

theorem psl_le_iff (ω k : ℕ) (a b : ChainsPoset ω k) : a ≤ b ↔ a.1 = b.1 ∧ a.2.val ≤ b.2.val := by
  obtain ⟨i, x⟩ := a
  obtain ⟨i', y⟩ := b
  constructor
  · intro h
    cases h with
    | fiber _ _ _ h2 => exact ⟨rfl, h2⟩
  · rintro ⟨h1, h2⟩
    simp only at h1
    subst h1
    exact (Sigma.mk_le_mk_iff).2 h2

theorem psl_width (ω k : ℕ) (hk : 1 ≤ k) :
    AppliedComb.Posets.width (ChainsPoset ω k) = ω := by
  classical
  unfold AppliedComb.Posets.width
  apply le_antisymm
  · apply Finset.sup_le
    intro A hA
    rw [Finset.mem_filter] at hA
    have hA' := hA.2
    have : A.card ≤ (Finset.univ : Finset (Fin ω)).card := by
      apply Finset.card_le_card_of_injOn (fun x => x.1)
      · intro x _; simp
      · intro x hx y hy hxy
        by_contra hne
        have hxy' : x.1 = y.1 := hxy
        rcases le_total x.2.val y.2.val with h | h
        · exact hA' (by exact_mod_cast hx) (by exact_mod_cast hy) hne ((psl_le_iff ω k x y).2 ⟨hxy', h⟩)
        · exact hA' (by exact_mod_cast hy) (by exact_mod_cast hx) (Ne.symm hne) ((psl_le_iff ω k y x).2 ⟨hxy'.symm, h⟩)
    simpa using this
  · have hmem : (Finset.univ.image (fun i : Fin ω => (⟨i, ⟨0, hk⟩⟩ : ChainsPoset ω k))) ∈
        (Finset.univ : Finset (Finset (ChainsPoset ω k))).filter
          (fun A : Finset (ChainsPoset ω k) => IsAntichain (· ≤ ·) (A : Set (ChainsPoset ω k))) := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro x hx y hy hne hle
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, rfl⟩ := hy
      rw [psl_le_iff] at hle
      apply hne
      have := hle.1
      simp only at this
      rw [this]
    have hc : (Finset.univ.image (fun i : Fin ω => (⟨i, ⟨0, hk⟩⟩ : ChainsPoset ω k))).card = ω := by
      rw [Finset.card_image_of_injective]
      · simp
      · intro i j h
        simpa using h
    calc ω = _ := hc.symm
      _ ≤ _ := Finset.le_sup (f := Finset.card) hmem

theorem psl_expectedScore_eq (ω k : ℕ) (μ : Finset (ChainsPoset ω k) → ℝ) (w : ChainsPoset ω k → ℝ) :
    expectedScore μ w = ∑ a, selProb μ a * w a := by
  classical
  unfold expectedScore selProb
  simp only [Finset.sum_mul]
  have : ∀ s : Finset (ChainsPoset ω k), μ s * ∑ a ∈ s, w a =
      ∑ a, if a ∈ s then μ s * w a else 0 := by
    intro s
    rw [Finset.mul_sum, ← Finset.sum_filter]
    congr 1
    ext a; simp
  simp only [this]
  rw [Finset.sum_comm]
  congr 1
  ext a
  rw [← Finset.sum_filter]

theorem psl_sum_selProb_le (ω k : ℕ) (μ : Finset (ChainsPoset ω k) → ℝ) (hμ : IsSelectionRule k μ) :
    ∑ a, selProb μ a ≤ k := by
  have h := psl_expectedScore_eq ω k μ (fun _ => 1)
  simp only [mul_one] at h
  rw [← h]
  unfold expectedScore
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  calc ∑ s, μ s * (s.card : ℝ) ≤ ∑ s, μ s * (k : ℝ) := by
        apply Finset.sum_le_sum
        intro s _
        by_cases hs : k < s.card
        · rw [hμ.2.2 s hs]; simp
        · have : (s.card : ℝ) ≤ k := by exact_mod_cast (not_lt.1 hs)
          exact mul_le_mul_of_nonneg_left this (hμ.1 s)
    _ = k := by rw [← Finset.sum_mul, hμ.2.1, one_mul]

theorem psl_exists_chain (ω k : ℕ) (hω : 1 ≤ ω)
    (μ : Finset (ChainsPoset ω k) → ℝ) (hμ : IsSelectionRule k μ) :
    ∃ i : Fin ω, ∑ j : Fin k, selProb μ ⟨i, j⟩ ≤ (k : ℝ) / ω := by
  have h1 := psl_sum_selProb_le ω k μ hμ
  rw [Fintype.sum_sigma] at h1
  have hne : (Finset.univ : Finset (Fin ω)).Nonempty := ⟨⟨0, hω⟩, Finset.mem_univ _⟩
  have h2 : ∑ i : Fin ω, ∑ j : Fin k, selProb μ ⟨i, j⟩ ≤ ∑ _i : Fin ω, (k : ℝ) / ω := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (ω : ℝ) ≠ 0 := by positivity
    rw [mul_div_cancel₀ _ this]
    exact h1
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le hne h2
  exact ⟨i, hi⟩

theorem solution (k ω : ℕ) (hk : 1 ≤ k) (hω : 1 ≤ ω) :
    ∃ (β : Type) (_ : PartialOrder β) (_ : Fintype β) (_ : DecidableEq β),
      AppliedComb.Posets.width β = ω ∧
      ∀ μ : Finset β → ℝ, IsSelectionRule k μ →
        ∀ ε : ℝ, 0 < ε →
          ∃ w : β → ℝ, PosetSecretary.ProxyLabel.IsConsistentScoring w ∧ 0 < PosetSecretary.ProxyLabel.opt w k ∧
            expectedScore μ w ≤ (1 + ε) * PosetSecretary.ProxyLabel.opt w k / ω := by
  refine ⟨ChainsPoset ω k, inferInstance, inferInstance, inferInstance, psl_width ω k hk, ?_⟩
  intro μ hμ ε hε
  obtain ⟨i, hi⟩ := psl_exists_chain ω k hω μ hμ
  obtain ⟨w, h1, h2, h3⟩ := PosetSecretary.LowerBound.exists_perturbation_expectedScore_le ω k hk hω μ hμ i hi 1 one_pos ε hε
  exact ⟨w, h1, by rw [h2]; exact one_pos, h3⟩

end
