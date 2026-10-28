-- Prove2me | solution 1 for SymBoolPCSP.CFixing.proposition_2_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T13:46:49.449082+00:00
-- url     : https://prove2.me/submissions/4b8184bc-e3f7-4d81-9d98-5219b5573bde

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

open SymBoolPCSP.CFixing in
theorem solution {τ : Type} [Fintype τ] {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool)
    (hPF : IsPromiseFamily 𝔸 𝔹) {L : ℕ} (f : (Fin L → Bool) → Bool) :
    (IsPolymorphism 𝔸 𝔹 f ∧ IsIdempotent f) ↔
      IsPolymorphism (withConsts 𝔸) (withConsts 𝔹) f := by
  constructor
  · rintro ⟨hf, h0, h1⟩
    intro R M hM
    cases R with
    | inl R => exact hf R M hM
    | inr b =>
      show (fun c : Fin 1 => f (fun l => M l c)) = fun _ => b
      funext c
      have hc : (fun l => M l c) = fun _ => b := by
        funext l
        have h' : M l = fun _ => b := hM l
        rw [h']
      rw [hc]
      cases b
      · exact h0
      · exact h1
  · intro h
    refine ⟨fun R M hM => h (Sum.inl R) M hM, ?_, ?_⟩
    · have h' : (fun c : Fin 1 => f (fun l => (fun _ _ => false : Fin L → Fin 1 → Bool) l c)) = fun _ => false :=
        h (Sum.inr false) (fun _ _ => false) (fun l => rfl)
      exact congrFun h' (0 : Fin 1)
    · have h' : (fun c : Fin 1 => f (fun l => (fun _ _ => true : Fin L → Fin 1 → Bool) l c)) = fun _ => true :=
        h (Sum.inr true) (fun _ _ => true) (fun l => rfl)
      exact congrFun h' (0 : Fin 1)
