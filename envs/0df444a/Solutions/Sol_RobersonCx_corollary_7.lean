-- Prove2me | solution 1 for RobersonCx.corollary_7
-- status  : ACCEPTED   (prove)
-- author  : @세리나
-- created : 2026-11-26T16:45:33.087399+00:00
-- url     : https://prove2.me/submissions/8ab40ff2-d819-4cb0-9837-5c84e9942767

import Definitions.Def_RobersonCx_InCl
import Definitions.Def_RobersonCx_QuotIsoTo
import Theorems.Thm_RobersonCx_proposition_5
import Theorems.Thm_RobersonCx_lemma_6

set_option autoImplicit false

open RobersonCx

private theorem homCountQuot_eq_homCount {V W X : Type}
    (F : SimpleGraph V) (τ : Equiv.Perm V) (H : SimpleGraph W) (GX : SimpleGraph X)
    (h : QuotIsoTo F τ H) : homCountQuot F τ GX = homCount H GX := by
  obtain ⟨e, hadj⟩ := h
  unfold homCountQuot homCount
  apply Nat.card_congr
  refine
    { toFun := fun φ =>
        ⟨fun v => φ.val (e.symm v), fun {u v} huv =>
          φ.property _ _ ((hadj _ _).mpr (by simpa only [Equiv.apply_symm_apply] using huv))⟩
      invFun := fun f =>
        ⟨fun O => f (e O), fun _ _ huv => f.map_adj ((hadj _ _).mp huv)⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro φ
    apply Subtype.ext
    funext O
    exact congrArg φ.val (e.symm_apply_apply O)
  · intro f
    apply DFunLike.ext
    intro v
    exact congrArg (fun w => f w) (e.apply_symm_apply v)

theorem solution {W : Type} [Finite W] (H : SimpleGraph W) (𝓕 : GraphClass) (P : Set ℕ)
    (hP : P.Infinite) (hprime : ∀ p ∈ P, p.Prime)
    (hF : ∀ p ∈ P, ∃ (V : Type) (_ : Finite V) (F : SimpleGraph V), 𝓕 V F ∧
      ∃ σ : F ≃g F, orderOf σ = p ∧ QuotIsoTo F σ.toEquiv H) :
    InCl 𝓕 H := by
  apply proposition_5 H P hP (fun p hp => (hprime p hp).pos) 𝓕
  intro p hp
  obtain ⟨V, hV, F, hmem, σ, hσ, hquot⟩ := hF p hp
  refine ⟨V, hV, F, hmem, ?_⟩
  intro X _ GX
  have hmod := @lemma_6 V hV F p (hprime p hp) σ hσ X ‹Finite X› GX
  rwa [homCountQuot_eq_homCount F σ.toEquiv H GX hquot] at hmod
