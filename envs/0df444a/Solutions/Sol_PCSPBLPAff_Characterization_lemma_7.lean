-- Prove2me | solution 1 for PCSPBLPAff.Characterization.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T10:11:30.417191+00:00
-- url     : https://prove2.me/submissions/2f930173-c793-4a94-b54d-0c417fb10652

import Mathlib
import Definitions.Def_PCSPBLPAff_Characterization_Setting
import Theorems.Thm_PCSPBLPAff_Characterization_lemma_16
import Theorems.Thm_PCSPBLPAff_Characterization_lemma_17
import Theorems.Thm_PCSPBLPAff_Characterization_observation_15

open PCSPBLPAff.Symmetric PCSPBLPAff.Characterization

/-- Finite instances detect homomorphisms from finite parts: if every instance satisfiable in
`𝔽` is satisfiable in the finite structure `𝔹`, then every finite induced substructure of `𝔽`
maps to `𝔹` (the signature `τ` may be infinite). -/
theorem PCSPBLPAff.Characterization.finite_part_hom_of_instances {τ : Type} {ar : τ → ℕ}
    {D B : Type} [Fintype B] (𝔽 : RelStruct τ ar D) (𝔹 : RelStruct τ ar B)
    (h : ∀ X : Instance τ ar, SatIn X 𝔽 → SatIn X 𝔹) (S : Finset D) :
    ∃ σ : D → B, ∀ R : τ, ∀ t ∈ 𝔽.rel R, (∀ k, t k ∈ S) → σ ∘ t ∈ 𝔹.rel R := by
  classical
  -- a fallback map `D → B` (if `D` is nonempty, `𝔹` is nonempty: the one-variable
  -- instance without constraints is satisfiable in `𝔽`).
  let g : D → B := if hD : Nonempty D then
      fun _ => (h ⟨1, 0, Fin.elim0, fun j => Fin.elim0 j⟩
        ⟨fun _ => hD.some, fun j => Fin.elim0 j⟩).choose 0
    else fun x => (hD ⟨x⟩).elim
  let S' := {x // x ∈ S}
  let n := Fintype.card S'
  let e : S' ≃ Fin n := Fintype.equivFin S'
  let m := Fintype.card (S' → B)
  let f : (S' → B) ≃ Fin m := Fintype.equivFin (S' → B)
  let ext : (S' → B) → D → B := fun φ x => if hx : x ∈ S then φ ⟨x, hx⟩ else g x
  by_contra hno
  push_neg at hno
  choose Rφ tφ htF htS htB using fun φ : S' → B => hno (ext φ)
  let X : Instance τ ar :=
    { n := n, m := m, sym := fun j => Rφ (f.symm j),
      scope := fun j k => e ⟨tφ (f.symm j) k, htS _ k⟩ }
  have hXF : SatIn X 𝔽 := by
    refine ⟨fun v => (e.symm v).1, fun j => ?_⟩
    have : (fun v => (e.symm v).1) ∘ X.scope j = tφ (f.symm j) := by
      funext k; simp [X]
    rw [this]; exact htF _
  obtain ⟨ψ, hψ⟩ := h X hXF
  let φ : S' → B := fun s => ψ (e s)
  have hj := hψ (f φ)
  apply htB (f.symm (f φ))
  convert hj using 1
  funext k
  simp only [X, Function.comp_apply, ext, dif_pos (htS _ k)]
  exact congrFun (Equiv.symm_apply_apply f φ) _

theorem PCSPBLPAff.Characterization.lemma_7_main {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A]
    [DecidableEq A] [Fintype B] (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B)
    (hT : IsPromiseTemplate 𝔸 𝔹) :
    CorrectlySolves 𝔸 𝔹 ↔ HasMinionHomToPol 𝔸 𝔹 := by
  rw [observation_15 𝔸 𝔹 hT, ← lemma_17 𝔸 𝔹 hT]
  constructor
  · intro h
    exact lemma_16 (freeStruct 𝔸) 𝔹 (finite_part_hom_of_instances (freeStruct 𝔸) 𝔹 h)
  · rintro ⟨σ, hσ⟩ X ⟨ν, hν⟩
    exact ⟨σ ∘ ν, fun j => hσ _ _ (hν j)⟩

/-- Lemma 7, p. 11. -/
theorem solution {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    (𝔸 : PCSPBLPAff.Symmetric.RelStruct τ ar A) (𝔹 : PCSPBLPAff.Symmetric.RelStruct τ ar B) (hT : PCSPBLPAff.Symmetric.IsPromiseTemplate 𝔸 𝔹) :
    PCSPBLPAff.Symmetric.CorrectlySolves 𝔸 𝔹 ↔ HasMinionHomToPol 𝔸 𝔹 :=
  PCSPBLPAff.Characterization.lemma_7_main 𝔸 𝔹 hT
