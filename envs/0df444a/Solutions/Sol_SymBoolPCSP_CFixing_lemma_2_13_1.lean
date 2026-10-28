-- Prove2me | solution 1 for SymBoolPCSP.CFixing.lemma_2_13_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:12:34.007014+00:00
-- url     : https://prove2.me/submissions/c6b98b52-b1f7-4e11-a35b-ab84861e13cb

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

open SymBoolPCSP.CFixing in
theorem solution {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) (hnd : IsNonDegenerateFamily 𝔸 𝔹)
    (hex : ∃ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f ∧ ¬ IsIdempotent f) :
    ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
      IsPolymorphism 𝔸 𝔹 f ↔
        (IsPolymorphism (withConsts 𝔸) (withConsts 𝔹) f ∨
          ∃ g : (Fin L → Bool) → Bool,
            IsPolymorphism (withConsts 𝔸) (withConsts (negStruct 𝔹)) g ∧ f = fun x => !g x) := by
  intro L f
  constructor
  · intro hf
    have h01 := hnd L f hf
    unfold IsNonDegenerate at h01
    -- constant rows
    have hconst : ∀ (b : Bool) (M : Fin L → Fin 1 → Bool), (∀ l, M l ∈ ({fun _ => b} : Set (Fin 1 → Bool))) →
        ∀ c, (fun l => M l c) = fun _ => b := by
      intro b M hM c
      funext l
      have := hM l
      rw [Set.mem_singleton_iff] at this
      rw [this]
    cases h0 : f (fun _ => false) <;> cases h1 : f (fun _ => true)
    · rw [h0, h1] at h01; exact absurd rfl h01
    · left
      intro R M hM
      cases R with
      | inl R => exact hf R M hM
      | inr b =>
        show (fun c : Fin 1 => f (fun l => M l c)) = fun _ => b
        funext c
        rw [hconst b M hM c]
        cases b
        · exact h0
        · exact h1
    · right
      refine ⟨fun x => !f x, ?_, ?_⟩
      · intro R M hM
        cases R with
        | inl R =>
          show (fun c => !f (fun l => M l c)) ∈ neg '' (𝔹.rel R)
          exact ⟨_, hf R M hM, rfl⟩
        | inr b =>
          show (fun c : Fin 1 => !f (fun l => M l c)) = fun _ => b
          funext c
          rw [hconst b M hM c]
          cases b
          · rw [h0]; rfl
          · rw [h1]; rfl
      · funext x
        simp
    · rw [h0, h1] at h01; exact absurd rfl h01
  · rintro (h | ⟨g, hg, rfl⟩)
    · intro R M hM
      exact h (Sum.inl R) M hM
    · intro R M hM
      obtain ⟨y, hy, hyeq⟩ := hg (Sum.inl R) M hM
      have : (fun c => !g (fun l => M l c)) = y := by
        funext c
        have := congrFun hyeq c
        simp only [neg] at this
        rw [← this, Bool.not_not]
      rw [this]; exact hy
