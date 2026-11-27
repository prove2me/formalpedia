-- Prove2me | solution 1 for PalomarZF207.nd_sound
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-27T00:03:06.541201+00:00
-- url     : https://prove2.me/submissions/9072c00d-82f7-4e4c-b936-bebf609e67ae

import Definitions.Def_palomar_zf207_history
import Definitions.Def_palomar_zf207_zf
import Definitions.Def_palomar_zf207_statement

open PalomarZF207

namespace SolNDSound

private theorem pushValue_comp_lift {V : Type} (σ : Nat → Nat) (s : Nat → V) (x : V) :
    (fun i => pushValue s x (lift σ i)) = pushValue (fun i => s (σ i)) x := by
  funext i
  cases i <;> rfl

private theorem eval_rename {V : Type} (E : V → V → Prop) :
    ∀ (f : Formula) (σ : Nat → Nat) (s : Nat → V),
      eval E (rename σ f) s ↔ eval E f (fun i => s (σ i))
  | .bot, _, _ => Iff.rfl
  | .mem _ _, _, _ => Iff.rfl
  | .eq _ _, _, _ => Iff.rfl
  | .and p q, σ, s => by
    simp only [rename, eval, eval_rename E p σ s, eval_rename E q σ s]
  | .or p q, σ, s => by
    simp only [rename, eval, eval_rename E p σ s, eval_rename E q σ s]
  | .imp p q, σ, s => by
    simp only [rename, eval, eval_rename E p σ s, eval_rename E q σ s]
  | .all p, σ, s => by
    constructor
    · intro h x
      have hx := (eval_rename E p (lift σ) (pushValue s x)).mp (h x)
      rwa [pushValue_comp_lift] at hx
    · intro h x
      apply (eval_rename E p (lift σ) (pushValue s x)).mpr
      rw [pushValue_comp_lift]
      exact h x
  | .ex p, σ, s => by
    constructor
    · rintro ⟨x, hx⟩
      have hx' := (eval_rename E p (lift σ) (pushValue s x)).mp hx
      rw [pushValue_comp_lift] at hx'
      exact ⟨x, hx'⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, (eval_rename E p (lift σ) (pushValue s x)).mpr ?_⟩
      rw [pushValue_comp_lift]
      exact hx

private theorem eval_shift {V : Type} (E : V → V → Prop) (f : Formula) (s : Nat → V) (x : V) :
    eval E (shift f) (pushValue s x) ↔ eval E f s :=
  eval_rename E f Nat.succ (pushValue s x)

private theorem eval_subst {V : Type} (E : V → V → Prop) (t : Nat) (f : Formula) (s : Nat → V) :
    eval E (subst t f) s ↔ eval E f (pushValue s (s t)) := by
  have hfn : (fun i => s (substMap t i)) = pushValue s (s t) := by
    funext i
    cases i <;> rfl
  rw [subst, eval_rename, hfn]

private def RowValid {V : Type} (E : V → V → Prop) : Row → Prop
  | .seq Γ a => ∀ s : Nat → V, (∀ g, g ∈ Γ → eval E g s) → eval E a s
  | .branches Γ a b c =>
      ∀ s : Nat → V, (∀ g, g ∈ Γ → eval E g s) → (eval E a s → eval E c s) ∧ (eval E b s → eval E c s)

private theorem nd_row_sound {V : Type} (E : V → V → Prop) {r : Row} (h : ND r) :
    RowValid E r := by
  induction h with
  | ctx hmem =>
    intro s hs; exact hs _ hmem
  | pc _ a b =>
    intro s _ hpeirce
    cases Classical.em (eval E a s) with
    | inl ha => exact ha
    | inr hna => exact hpeirce (fun ha => False.elim (hna ha))
  | ii _ ih =>
    intro s hs ha
    apply ih s
    intro g hg
    cases hg with
    | head => exact ha
    | tail _ hmem => exact hs g hmem
  | ie _ _ ih1 ih2 =>
    intro s hs; exact ih1 s hs (ih2 s hs)
  | exp _ ih =>
    intro s hs; exact False.elim (ih s hs)
  | ci _ _ ih1 ih2 =>
    intro s hs; exact ⟨ih1 s hs, ih2 s hs⟩
  | ce1 _ ih =>
    intro s hs; exact (ih s hs).1
  | ce2 _ ih =>
    intro s hs; exact (ih s hs).2
  | di1 _ ih =>
    intro s hs; exact Or.inl (ih s hs)
  | di2 _ ih =>
    intro s hs; exact Or.inr (ih s hs)
  | branchPair _ _ ih1 ih2 =>
    intro s hs
    constructor
    · intro ha
      apply ih1 s
      intro g hg
      cases hg with
      | head => exact ha
      | tail _ hmem => exact hs g hmem
    · intro hb
      apply ih2 s
      intro g hg
      cases hg with
      | head => exact hb
      | tail _ hmem => exact hs g hmem
  | de _ _ ih1 ih2 =>
    intro s hs
    cases ih1 s hs with
    | inl ha => exact (ih2 s hs).1 ha
    | inr hb => exact (ih2 s hs).2 hb
  | wk hsub _ ih =>
    intro s hs; exact ih s (fun g hg => hs g (hsub g hg))
  | allI _ ih =>
    intro s hs x
    apply ih (pushValue s x)
    intro g hg
    rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩
    exact (eval_shift E g0 s x).mpr (hs g0 hg0)
  | allE t _ ih =>
    intro s hs
    exact (eval_subst E t _ s).mpr (ih s hs (s t))
  | exI t _ ih =>
    intro s hs
    exact ⟨s t, (eval_subst E t _ s).mp (ih s hs)⟩
  | exE _ _ ih1 ih2 =>
    intro s hs
    obtain ⟨x, hx⟩ := ih1 s hs
    apply (eval_shift E _ s x).mp
    apply ih2 (pushValue s x)
    intro g hg
    cases hg with
    | head => exact hx
    | tail _ hmem =>
      rcases List.mem_map.mp hmem with ⟨g0, hg0, rfl⟩
      exact (eval_shift E g0 s x).mpr (hs g0 hg0)

end SolNDSound

theorem solution (p : Formula) :
    Provable p → ∀ (V : Type) (E : V → V → Prop), Nonempty V → Model E → ∀ s : Nat → V, eval E p s := by
  rintro ⟨Γ, hAx, hND⟩ V E _ hModel s
  exact SolNDSound.nd_row_sound E hND s (fun g hg => hModel g (hAx g hg) s)
