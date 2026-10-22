-- Prove2me | solution 1 for SymBoolPCSP.Galois.chain
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:12:19.378988+00:00
-- url     : https://prove2.me/submissions/7e255123-9498-41b0-9d44-4acdd6a1cf70

import Mathlib
import Definitions.Def_SymBoolPCSP_Galois_Basic
set_option autoImplicit false
open SymBoolPCSP.Galois PCSPBLPAff.Symmetric

theorem solution {τ τ' : Type} [Fintype τ] {ar : τ → ℕ} {ar' : τ' → ℕ}
    {D : Type} [Fintype D] [DecidableEq D]
    (𝔸 𝔹 : RelStruct τ ar D) (𝔸' 𝔹' : RelStruct τ' ar' D)
    (hΓ : IsPromiseFamily 𝔸 𝔹) (hΓ' : IsPromiseFamily 𝔸' 𝔹')
    (hPol : PolSubset 𝔸 𝔹 𝔸' 𝔹') (R' : τ') (m : ℕ) (e : Fin m ≃ 𝔸'.rel R') :
    𝔸'.rel R' ⊆ evalAt (fun j => (e j : Fin (ar' R') → D)) (SL 𝔸 m) ∧
      evalAt (fun j => (e j : Fin (ar' R') → D)) (SL 𝔸 m) ⊆
        evalAt (fun j => (e j : Fin (ar' R') → D)) (TL 𝔸 𝔹 m) ∧
      evalAt (fun j => (e j : Fin (ar' R') → D)) (TL 𝔸 𝔹 m) ⊆ 𝔹'.rel R' := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    refine ⟨fun v => v (e.symm ⟨t, ht⟩), ?_, ?_⟩
    · intro R M hM
      exact hM _
    · funext i
      simp [yvec]
  · rintro t ⟨f, hf, rfl⟩
    refine ⟨f, ?_, rfl⟩
    intro R M hM
    exact hΓ R (hf R M hM)
  · rintro t ⟨f, hf, rfl⟩
    have h := hPol m f hf R' (fun j => (e j : Fin (ar' R') → D)) (fun l => (e l).2)
    exact h
