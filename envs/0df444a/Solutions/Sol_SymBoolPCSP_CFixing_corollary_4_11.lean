-- Prove2me | solution 1 for SymBoolPCSP.CFixing.corollary_4_11
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:10:11.074075+00:00
-- url     : https://prove2.me/submissions/7678e136-fd55-4f72-890c-94ea97bcd6f2

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

open SymBoolPCSP.CFixing in
theorem solution {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹)
    (hidem : IsIdempotentFamily 𝔸 𝔹) (L₁ L₂ : ℕ) (hL₁ : Odd L₁) (hL₂ : Odd L₂)
    (hPar : ¬ IsPolymorphism 𝔸 𝔹 (Par L₁)) (hAT : ¬ IsPolymorphism 𝔸 𝔹 (AT L₂))
    (c : ℕ) (hc : ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f →
      (Finset.univ.filter (fun i : Fin L => f (indicator {i}) = true)).card ≤ c) :
    ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f →
      ∀ (ℓ : ℕ) (S : Fin ℓ → Finset (Fin L)), (∀ i j, i ≠ j → Disjoint (S i) (S j)) →
        (∀ i, f (indicator (S i)) = true) → ℓ ≤ c := by
  intro L f hf ℓ S hdisj hS
  let π : Fin L → Fin (ℓ + 1) := fun j =>
    if h : ∃ i, j ∈ S i then (Classical.choose h).succ else 0
  have hπ : ∀ i j, π j = i.succ ↔ j ∈ S i := by
    intro i j
    simp only [π]
    split_ifs with h
    · have hcs := Classical.choose_spec h
      constructor
      · intro e
        rw [Fin.succ_inj] at e
        rw [← e]; exact hcs
      · intro hj
        rw [Fin.succ_inj]
        by_contra hne
        exact Finset.disjoint_left.mp (hdisj _ _ hne) hcs hj
    · constructor
      · intro e; exact absurd e.symm (Fin.succ_ne_zero i)
      · intro hj; exact absurd ⟨i, hj⟩ h
  let g : (Fin (ℓ + 1) → Bool) → Bool := fun x => f (x ∘ π)
  have hg : IsPolymorphism 𝔸 𝔹 g := by
    intro R M hM
    exact hf R (fun j => M (π j)) (fun j => hM (π j))
  have hgi : ∀ i : Fin ℓ, g (indicator {i.succ}) = true := by
    intro i
    have e : (indicator {i.succ} ∘ π) = indicator (S i) := by
      funext j
      simp only [Function.comp, indicator, Finset.mem_singleton]
      rw [decide_eq_decide]
      exact hπ i j
    show f (indicator {i.succ} ∘ π) = true
    rw [e]; exact hS i
  have hcard := hc (ℓ + 1) g hg
  have hsub : (Finset.univ.image Fin.succ : Finset (Fin (ℓ + 1))) ⊆
      Finset.univ.filter (fun i : Fin (ℓ + 1) => g (indicator {i}) = true) := by
    intro k hk
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgi i⟩
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (Fin.succ_injective _), Finset.card_univ,
    Fintype.card_fin] at h2
  omega
