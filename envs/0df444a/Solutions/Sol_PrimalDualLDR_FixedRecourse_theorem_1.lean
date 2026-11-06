-- Prove2me | solution 1 for PrimalDualLDR.FixedRecourse.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:42:46.660558+00:00
-- url     : https://prove2.me/submissions/99e961c4-72ee-4c45-89bb-5b960feeb872

import Mathlib
import Definitions.Def_PrimalDualLDR_FixedRecourse_Basic
import Definitions.Def_PrimalDualLDR_FixedRecourse_Setting
import Definitions.Def_PrimalDualLDR_FixedRecourse_Problems
import Theorems.Thm_PrimalDualLDR_FixedRecourse_sec_2_2_constraints
import Theorems.Thm_PrimalDualLDR_FixedRecourse_proposition_1
import Theorems.Thm_PrimalDualLDR_FixedRecourse_sec_2_4_eq_2_6
import Theorems.Thm_PrimalDualLDR_FixedRecourse_proposition_4

open MeasureTheory Matrix

open PrimalDualLDR.FixedRecourse in
theorem solution (σ : Setting) (hσ : σ.Standing)
    (hW : ∃ i : Fin σ.l, 2 ≤ i.val ∧ σ.W i ≠ 0) (hsf : σ.StrictlyFeasible) :
    σ.valSPu = σ.valLP23 ∧ σ.valSPl = σ.valLP28 := by
  refine ⟨?_, (sec_2_4_eq_2_6 σ hσ).trans (proposition_4 σ hσ hW hsf)⟩
  have hne : (polyhedron σ.W σ.h).Nonempty := hσ.2.1
  -- feasibility in SP^u, for fixed `X`, is equivalent to feasibility in (2.3)
  have key : ∀ X : Matrix (Fin σ.n) (Fin σ.k) ℝ,
      (∃ S, (X, S) ∈ σ.feasSPu) ↔ (∃ Λ, (X, Λ) ∈ σ.feasLP23) := by
    intro X
    constructor
    · rintro ⟨S, hS⟩
      have hS' := (Filter.eventually_and.1 (show ∀ᵐ ξ ∂σ.P, _ ∧ _ from hS))
      obtain ⟨_, h2, h3⟩ := sec_2_2_constraints σ hσ X S
      have heq : σ.A * X + S = σ.B := h3.1 hS'.1
      have hnn := h2.1 hS'.2
      have hrow : ∀ i, ∃ lam : Fin σ.l → ℝ, (∀ j, 0 ≤ lam j) ∧ σ.Wᵀ.mulVec lam = S i ∧
          0 ≤ σ.h ⬝ᵥ lam := by
        intro i
        refine (proposition_1 σ.W σ.h hne (S i)).1 ?_
        intro ξ hξ
        exact hnn ξ hξ i
      choose lam hl0 hlW hlh using hrow
      refine ⟨Matrix.of lam, ?_, ?_, ?_⟩
      · have : Matrix.of lam * σ.W = S := by
          ext i j
          rw [← hlW i]
          simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
        simpa [this] using heq
      · intro i
        change 0 ≤ (fun j => lam i j) ⬝ᵥ σ.h
        rw [dotProduct_comm]; exact hlh i
      · intro i j; exact hl0 i j
    · rintro ⟨Λ, hAX, hΛh, hΛ⟩
      refine ⟨Λ * σ.W, ?_⟩
      obtain ⟨_, h2, h3⟩ := sec_2_2_constraints σ hσ X (Λ * σ.W)
      have hnn : ∀ ξ ∈ σ.Xi, ∀ i, 0 ≤ ((Λ * σ.W).mulVec ξ) i := by
        intro ξ hξ i
        have := (proposition_1 σ.W σ.h hne ((Λ * σ.W) i)).2
          ⟨Λ i, fun j => hΛ i j, by
            ext j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm],
           by rw [dotProduct_comm]; exact hΛh i⟩ ξ hξ
        exact this
      exact Filter.eventually_and.2 ⟨h3.2 hAX, h2.2 hnn⟩
  apply le_antisymm
  · refine le_iInf₂ fun q hq => ?_
    obtain ⟨S, hS⟩ := (key q.1).2 ⟨q.2, hq⟩
    exact iInf₂_le (f := fun p (_ : p ∈ σ.feasSPu) => ((σ.linObj p.1 : ℝ) : EReal)) (q.1, S) hS
  · refine le_iInf₂ fun p hp => ?_
    obtain ⟨Λ, hΛ⟩ := (key p.1).1 ⟨p.2, hp⟩
    exact iInf₂_le (f := fun q (_ : q ∈ σ.feasLP23) => ((σ.linObj q.1 : ℝ) : EReal)) (p.1, Λ) hΛ
