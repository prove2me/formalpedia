-- Prove2me | solution 1 for SymBoolPCSP.CFixing.lemma_4_10
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T18:28:03.766382+00:00
-- url     : https://prove2.me/submissions/58155851-973c-41fe-8382-dd2c56a90bed

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic
import Theorems.Thm_SymBoolPCSP_CFixing_lemma_4_5
import Theorems.Thm_SymBoolPCSP_CFixing_lemma_4_9_bounded_explicit
import Theorems.Thm_SymBoolPCSP_CFixing_sum_conditions_of_relax_one
import Theorems.Thm_SymBoolPCSP_CFixing_sum_conditions_of_relax_zero
import Theorems.Thm_SymBoolPCSP_CFixing_par_minor_of_parity

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

theorem lemma_4_10 {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹)
    (hidem : IsIdempotentFamily 𝔸 𝔹) (L₁ L₂ : ℕ) (hL₁ : Odd L₁) (hL₂ : Odd L₂)
    (hPar : ¬ IsPolymorphism 𝔸 𝔹 (Par L₁)) (hAT : ¬ IsPolymorphism 𝔸 𝔹 (AT L₂)) :
    ∃ c : ℕ, ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f →
      (Finset.univ.filter (fun i : Fin L => f (indicator {i}) = true)).card ≤ c := by
  classical
  obtain ⟨k, hcase⟩ := lemma_4_5 𝔸 𝔹 hPF hsym hfold hidem L₂ hL₂ hAT
  have hn : ∃ n, 2 ≤ n ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f →
      ∀ (T : Finset (Fin L)) (S₀ S₁ : Set ℕ),
      (∀ s, s ∈ S₀ ↔ ∀ X ⊆ T, X.card = s → f (indicator X) = false) →
      (∀ s, s ∈ S₁ ↔ ∀ X ⊆ T, X.card = s → f (indicator X) = true) →
      (∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ∈ S₀) ∧
      (∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) → a + ∑ i, b i ∈ S₁) := by
    rcases hcase with ⟨hk, hR⟩ | ⟨hk, b, hb1, hbk, hR⟩
    · exact ⟨k - 1, by omega, fun L f hf T S₀ S₁ h0 h1 =>
        sum_conditions_of_relax_one (by omega) f (hfold L f hf) (hR L f hf) T S₀ S₁ h0 h1⟩
    · exact ⟨k - b + 1, by omega, fun L f hf T S₀ S₁ h0 h1 =>
        sum_conditions_of_relax_zero hb1 hbk f (hfold L f hf) (hR L f hf) T S₀ S₁ h0 h1⟩
  obtain ⟨n, hn2, hcond⟩ := hn
  refine ⟨(1 + (2 * n - 2) * (3 * n - 4)) + L₁ * ((1 + (2 * n - 2) * (3 * n - 4)) + 1),
    fun L f hf => ?_⟩
  generalize hC : 1 + (2 * n - 2) * (3 * n - 4) = C
  set T := univ.filter (fun i : Fin L => f (indicator {i}) = true) with hT
  by_contra hlt
  push Not at hlt
  obtain ⟨c1, c2⟩ := hcond L f hf T {s | ∀ X ⊆ T, X.card = s → f (indicator X) = false}
    {s | ∀ X ⊆ T, X.card = s → f (indicator X) = true} (fun s => Iff.rfl) (fun s => Iff.rfl)
  have h0 : 0 ∈ {s | ∀ X ⊆ T, X.card = s → f (indicator X) = false} := by
    intro X _ hX
    rw [Finset.card_eq_zero.mp hX]
    have hind : indicator (∅ : Finset (Fin L)) = fun _ => false := by
      funext i; simp [indicator]
    rw [hind]; exact (hidem L f hf).1
  have h1 : 1 ∈ {s | ∀ X ⊆ T, X.card = s → f (indicator X) = true} := by
    intro X hXT hX
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hX
    have := hXT (mem_singleton_self i)
    rw [hT, mem_filter] at this; exact this.2
  have key := lemma_4_9_bounded_explicit n T.card (by omega) _ _ h0 h1
    (fun b hb _ => c1 b hb) (fun a ha b hb _ => c2 a ha b hb)
  rw [if_neg (by omega), hC] at key
  rcases Nat.even_or_odd n with he | ho
  · have hpar : ∀ X ⊆ T, C ≤ X.card → f (indicator X) = decide (X.card % 2 = 1) := by
      intro X hXT hCX
      have := key.2 he X.card hCX (Finset.card_le_card hXT)
      rcases Nat.even_or_odd X.card with hx | hx
      · rw [this.1 hx X hXT rfl]; simp [Nat.even_iff.mp hx]
      · rw [this.2 hx X hXT rfl]; simp [Nat.odd_iff.mp hx]
    obtain ⟨π, hπ⟩ := par_minor_of_parity f (hfold L f hf) (hidem L f hf).1 hL₁ T C hpar
      ((Nat.le_add_left _ _).trans hlt.le)
    apply hPar
    have hP : Par L₁ = fun y => f (fun i => y (π i)) := funext fun y => (hπ y).symm
    rw [hP]
    intro R M hM
    exact hf R (fun l => M (π l)) (fun l => hM _)
  · obtain ⟨hA, hB⟩ := key.1 ho ((Nat.le_add_right _ _).trans hlt.le)
    obtain ⟨X, hXT, hXc⟩ := Finset.exists_subset_card_eq
      (show C ≤ T.card from (Nat.le_add_right _ _).trans hlt.le)
    have := (hA X hXT hXc).symm.trans (hB X hXT hXc)
    simp at this

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hsym : IsSymmetricFamily 𝔸 𝔹) (hfold : IsFoldedFamily 𝔸 𝔹)
    (hidem : IsIdempotentFamily 𝔸 𝔹) (L₁ L₂ : ℕ) (hL₁ : Odd L₁) (hL₂ : Odd L₂)
    (hPar : ¬ IsPolymorphism 𝔸 𝔹 (Par L₁)) (hAT : ¬ IsPolymorphism 𝔸 𝔹 (AT L₂)) :
    ∃ c : ℕ, ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f →
      (Finset.univ.filter (fun i : Fin L => f (indicator {i}) = true)).card ≤ c :=
  SymBoolPCSP.CFixing.lemma_4_10 𝔸 𝔹 hPF hsym hfold hidem L₁ L₂ hL₁ hL₂ hPar hAT
