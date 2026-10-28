-- Prove2me | solution 1 for ThresholdTheorem.weight_le_of_disjoint_pair_witness
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T20:47:35.501697+00:00
-- url     : https://prove2.me/submissions/695fc543-779e-4037-b9c8-6b4fe3c63996

import Mathlib

namespace ThresholdTheorem
theorem weight_le_aux {r : ℕ} (w : Fin r → ℝ)
    (F : Fin r → Finset (ℕ × ℕ)) (e : ℝ) (_he : 0 ≤ e) (hw : ∀ i, 0 ≤ w i)
    (hF : ∀ S : Finset (ℕ × ℕ),
      ∑ i ∈ Finset.univ.filter (fun i => S ⊆ F i), w i ≤ e ^ S.card)
    (M : ℕ) (pairs : ℕ × ℕ → Finset (Finset (ℕ × ℕ)))
    (Φ : Finset (ℕ × ℕ) → Finset (ℕ × ℕ))
    (hcard : ∀ ℓ, (pairs ℓ).card ≤ M) (htwo : ∀ ℓ, ∀ p ∈ pairs ℓ, p.card = 2)
    (hwit : ∀ (G S : Finset (ℕ × ℕ)), S ⊆ Φ G →
      ∃ g : ℕ × ℕ → Finset (ℕ × ℕ), (∀ ℓ ∈ S, g ℓ ∈ pairs ℓ ∧ g ℓ ⊆ G) ∧
        ∀ ℓ₁ ∈ S, ∀ ℓ₂ ∈ S, ℓ₁ ≠ ℓ₂ → Disjoint (g ℓ₁) (g ℓ₂))
    (S : Finset (ℕ × ℕ)) :
    ∑ i ∈ Finset.univ.filter (fun i => S ⊆ Φ (F i)), w i ≤ ((M : ℝ) * e ^ 2) ^ S.card := by
  classical
  set T := S.pi pairs with hT
  let D : ((a : ℕ × ℕ) → a ∈ S → Finset (ℕ × ℕ)) → Prop := fun g =>
    ∀ ℓ₁ (h₁ : ℓ₁ ∈ S) ℓ₂ (h₂ : ℓ₂ ∈ S), ℓ₁ ≠ ℓ₂ → Disjoint (g ℓ₁ h₁) (g ℓ₂ h₂)
  let U : ((a : ℕ × ℕ) → a ∈ S → Finset (ℕ × ℕ)) → Finset (ℕ × ℕ) := fun g =>
    S.attach.biUnion (fun x => g x.1 x.2)
  -- step 1: pointwise domination
  have step1 : ∑ i ∈ Finset.univ.filter (fun i => S ⊆ Φ (F i)), w i ≤
      ∑ i, ∑ g ∈ T, (if D g ∧ U g ⊆ F i then w i else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun i _ => ?_
    split_ifs with hS
    · obtain ⟨g0, hg0, hdis⟩ := hwit (F i) S hS
      let g' : (a : ℕ × ℕ) → a ∈ S → Finset (ℕ × ℕ) := fun a _ => g0 a
      have hg'T : g' ∈ T := by
        rw [hT, Finset.mem_pi]; intro a ha; exact (hg0 a ha).1
      have hD : D g' ∧ U g' ⊆ F i := by
        refine ⟨fun ℓ₁ h₁ ℓ₂ h₂ hne => hdis ℓ₁ h₁ ℓ₂ h₂ hne, ?_⟩
        intro x hx
        simp only [U, Finset.mem_biUnion] at hx
        obtain ⟨⟨a, ha⟩, _, hxa⟩ := hx
        exact (hg0 a ha).2 hxa
      have := Finset.single_le_sum (f := fun g => if D g ∧ U g ⊆ F i then w i else 0)
        (fun g _ => by split_ifs <;> simp [hw i]) hg'T
      simpa [hD] using this
    · exact Finset.sum_nonneg fun g _ => by split_ifs <;> simp [hw i]
  -- step 2: per choice function bound
  have step2 : ∀ g ∈ T, ∑ i, (if D g ∧ U g ⊆ F i then w i else 0) ≤ (e ^ 2) ^ S.card := by
    intro g hg
    by_cases hDg : D g
    · have hU : (U g).card = 2 * S.card := by
        simp only [U]
        rw [Finset.card_biUnion]
        · rw [Finset.sum_congr rfl (g := fun _ => 2)]
          · simp [mul_comm]
          · intro x _
            rw [hT, Finset.mem_pi] at hg
            exact htwo x.1 _ (hg x.1 x.2)
        · intro x _ y _ hxy
          exact hDg x.1 x.2 y.1 y.2 (fun h => hxy (Subtype.ext h))
      have h1 : ∑ i, (if D g ∧ U g ⊆ F i then w i else 0) =
          ∑ i ∈ Finset.univ.filter (fun i => U g ⊆ F i), w i := by
        rw [Finset.sum_filter]; simp [hDg]
      rw [h1, ← pow_mul, ← hU]
      exact hF (U g)
    · have : ∑ i, (if D g ∧ U g ⊆ F i then w i else 0) = 0 := by simp [hDg]
      rw [this]; positivity
  calc ∑ i ∈ Finset.univ.filter (fun i => S ⊆ Φ (F i)), w i
      ≤ ∑ i, ∑ g ∈ T, (if D g ∧ U g ⊆ F i then w i else 0) := step1
    _ = ∑ g ∈ T, ∑ i, (if D g ∧ U g ⊆ F i then w i else 0) := Finset.sum_comm
    _ ≤ ∑ g ∈ T, (e ^ 2) ^ S.card := Finset.sum_le_sum step2
    _ = T.card * (e ^ 2) ^ S.card := by simp
    _ ≤ (M : ℝ) ^ S.card * (e ^ 2) ^ S.card := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [hT, Finset.card_pi]
        have : (∏ a ∈ S, (pairs a).card) ≤ M ^ S.card := by
          calc (∏ a ∈ S, (pairs a).card) ≤ ∏ _a ∈ S, M :=
                Finset.prod_le_prod' fun a _ => hcard a
            _ = M ^ S.card := by simp
        exact_mod_cast this
    _ = ((M : ℝ) * e ^ 2) ^ S.card := by rw [mul_pow]
end ThresholdTheorem

theorem solution {r : ℕ} (w : Fin r → ℝ)
    (F : Fin r → Finset (ℕ × ℕ)) (e : ℝ) (he : 0 ≤ e) (hw : ∀ i, 0 ≤ w i)
    (hF : ∀ S : Finset (ℕ × ℕ),
      ∑ i ∈ Finset.univ.filter (fun i => S ⊆ F i), w i ≤ e ^ S.card)
    (M : ℕ) (pairs : ℕ × ℕ → Finset (Finset (ℕ × ℕ)))
    (Φ : Finset (ℕ × ℕ) → Finset (ℕ × ℕ))
    (hcard : ∀ ℓ, (pairs ℓ).card ≤ M) (htwo : ∀ ℓ, ∀ p ∈ pairs ℓ, p.card = 2)
    (hwit : ∀ (G S : Finset (ℕ × ℕ)), S ⊆ Φ G →
      ∃ g : ℕ × ℕ → Finset (ℕ × ℕ), (∀ ℓ ∈ S, g ℓ ∈ pairs ℓ ∧ g ℓ ⊆ G) ∧
        ∀ ℓ₁ ∈ S, ∀ ℓ₂ ∈ S, ℓ₁ ≠ ℓ₂ → Disjoint (g ℓ₁) (g ℓ₂))
    (S : Finset (ℕ × ℕ)) :
    ∑ i ∈ Finset.univ.filter (fun i => S ⊆ Φ (F i)), w i ≤ ((M : ℝ) * e ^ 2) ^ S.card :=
  ThresholdTheorem.weight_le_aux w F e he hw hF M pairs Φ hcard htwo hwit S

