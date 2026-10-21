-- Prove2me | solution 1 for STLC.beta_eta_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-21T01:45:12.721787+00:00
-- url     : https://prove2.me/submissions/8daff6ac-0ada-4a93-8410-a5e358283647

import Definitions.Def_STLC_core

/-! Soundness of beta-eta for the set-valued interpretation: the proof is by
induction on the derivation; the beta case is the substitution lemma and the eta
case is the renaming lemma. -/

namespace STLC

theorem CtxMap.cons_lift {X : Nat → Type} {Γ Δ : List Ty} {σ : Ty}
    (m : CtxMap Γ Δ) (v : interp X σ) (ρ : Env X Δ) :
    (fun τ x => Env.get (Env.cons v ρ) ((CtxMap.lift m).map x))
      = Env.cons v (fun τ x => Env.get ρ (m.map x)) := by
  funext τ x
  cases x with
  | z => rfl
  | s y => rfl

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

theorem Tm.eval_subst {X : Nat → Type} {Γ Δ : List Ty} (s : Sub Γ Δ) :
    ∀ {τ : Ty} (t : Tm Γ τ) (ρ : Env X Δ),
      Tm.eval (Tm.subst s t) ρ = Tm.eval t (Env.subst s ρ)
  | _, .var x, ρ => rfl
  | _, .lam t, ρ => by
    funext v
    simp only [Tm.subst, Tm.eval]
    rw [Tm.eval_subst (Sub.lift s) t (Env.cons v ρ), Env.subst_lift]
  | _, .app f a, ρ => by
    simp only [Tm.subst, Tm.eval]
    rw [Tm.eval_subst s f ρ, Tm.eval_subst s a ρ]

theorem Env.subst_single {X : Nat → Type} {Γ : List Ty} {σ : Ty} (a : Tm Γ σ)
    (ρ : Env X Γ) :
    Env.subst (Sub.single a) ρ = Env.cons (Tm.eval a ρ) ρ := by
  funext τ x
  cases x with
  | z => rfl
  | s y =>
    simp only [Env.subst, Sub.single_s]
    rfl

end STLC

open STLC

theorem solution {X : Nat → Type} :
    {Γ : List Ty} → {τ : Ty} → {t u : Tm Γ τ} → BE t u → (ρ : Env X Γ) →
      Tm.eval t ρ = Tm.eval u ρ
  | _, _, _, _, .refl t, ρ => rfl
  | _, _, _, _, .symm h, ρ => (solution h ρ).symm
  | _, _, _, _, .trans h1 h2, ρ => (solution h1 ρ).trans (solution h2 ρ)
  | _, _, _, _, .lam_congr h, ρ => by
    funext v
    exact solution h (Env.cons v ρ)
  | _, _, _, _, .app_congr hf ha, ρ => by
    simp only [Tm.eval]
    rw [solution hf ρ, solution ha ρ]
  | _, _, _, _, .beta t a, ρ => by
    simp only [Tm.eval]
    rw [Tm.eval_subst, Env.subst_single]
  | _, _, _, _, .eta t, ρ => by
    funext v
    simp only [Tm.eval]
    rw [Tm.eval_ren (CtxMap.wk _) t (Env.cons v ρ)]
    rfl
