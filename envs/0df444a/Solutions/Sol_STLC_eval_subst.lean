-- Prove2me | solution 1 for STLC.eval_subst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-21T01:45:11.786757+00:00
-- url     : https://prove2.me/submissions/50a07b29-2c3e-42a9-9fe2-58398311fd25

import Definitions.Def_STLC_core

/-! Proof of the substitution lemma for the set-valued interpretation of the
simply typed lambda calculus. Two auxiliary lemmas are proved on the way: the
renaming lemma, and the fact that lifting a substitution commutes with extending
the environment. -/

namespace STLC

/-- Extending an environment commutes with lifting a context morphism. -/
theorem CtxMap.cons_lift {X : Nat → Type} {Γ Δ : List Ty} {σ : Ty}
    (m : CtxMap Γ Δ) (v : interp X σ) (ρ : Env X Δ) :
    (fun τ x => Env.get (Env.cons v ρ) ((CtxMap.lift m).map x))
      = Env.cons v (fun τ x => Env.get ρ (m.map x)) := by
  funext τ x
  cases x with
  | z => rfl
  | s y => rfl

/-- **Renaming lemma**: renaming along a context morphism is substitution of the
induced environment. -/
theorem Tm.eval_ren {X : Nat → Type} {Γ Δ : List Ty} (m : CtxMap Γ Δ) :
    ∀ {τ : Ty} (t : Tm Γ τ) (ρ : Env X Δ),
      Tm.eval (Tm.ren m t) ρ = Tm.eval t (fun τ x => Env.get ρ (m.map x))
  | _, .var x, ρ => rfl
  | _, .lam t, ρ => by
    funext v
    simp only [Tm.ren, Tm.eval]
    rw [Tm.eval_ren (CtxMap.lift m) t (Env.cons v ρ), CtxMap.cons_lift]
  | _, .app f a, ρ => by
    simp only [Tm.ren, Tm.eval]
    rw [Tm.eval_ren m f ρ, Tm.eval_ren m a ρ]

/-- Lifting a substitution commutes with extending the environment. -/
theorem Env.subst_lift {X : Nat → Type} {Γ Δ : List Ty} {σ : Ty}
    (s : Sub Γ Δ) (v : interp X σ) (ρ : Env X Δ) :
    Env.subst (Sub.lift s) (Env.cons v ρ) = Env.cons v (Env.subst s ρ) := by
  funext τ x
  cases x with
  | z => rfl
  | s y =>
    simp only [Env.subst, Sub.lift_s]
    rw [Tm.eval_ren (CtxMap.wk σ) (s.sub y) (Env.cons v ρ)]
    rfl

end STLC

open STLC

theorem solution {X : Nat → Type} {Γ Δ : List Ty} (s : Sub Γ Δ) :
    ∀ {τ : Ty} (t : Tm Γ τ) (ρ : Env X Δ),
      Tm.eval (Tm.subst s t) ρ = Tm.eval t (Env.subst s ρ)
  | _, .var x, ρ => rfl
  | _, .lam t, ρ => by
    funext v
    simp only [Tm.subst, Tm.eval]
    rw [solution (Sub.lift s) t (Env.cons v ρ), Env.subst_lift]
  | _, .app f a, ρ => by
    simp only [Tm.subst, Tm.eval]
    rw [solution s f ρ, solution s a ρ]
