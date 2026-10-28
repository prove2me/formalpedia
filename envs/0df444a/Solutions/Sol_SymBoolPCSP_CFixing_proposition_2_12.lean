-- Prove2me | solution 1 for SymBoolPCSP.CFixing.proposition_2_12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:07:23.362054+00:00
-- url     : https://prove2.me/submissions/cb76a816-7e0a-4707-896a-982154236b58

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

open SymBoolPCSP.CFixing in
theorem solution {k L : ℕ} (P Q : Set (Fin k → Bool)) (hPQ : P ⊆ Q)
    (f : (Fin L → Bool) → Bool) (hf : PolOf P Q f) (hnd : IsNonDegenerate f)
    (hni : ¬ IsIdempotent f) :
    P ⊆ negRel Q ∧ IsIdempotent (fun x => !f x) ∧ PolOf P (negRel Q) (fun x => !f x) := by
  unfold IsNonDegenerate at hnd
  unfold IsIdempotent at hni
  have h01 : f (fun _ => false) = true ∧ f (fun _ => true) = false := by
    cases h0 : f (fun _ => false) <;> cases h1 : f (fun _ => true) <;> simp_all
  obtain ⟨h0, h1⟩ := h01
  have hb : ∀ b : Bool, f (fun _ => b) = !b := by
    intro b; cases b
    · exact h0
    · exact h1
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have := hf (fun _ => x) (fun _ => hx)
    refine ⟨_, this, ?_⟩
    funext c
    simp only [neg]
    rw [hb]
    simp
  · unfold IsIdempotent
    simp [h0, h1]
  · intro M hM
    exact ⟨_, hf M hM, rfl⟩
