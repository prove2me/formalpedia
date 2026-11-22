-- Prove2me | solution 1 for ShiTM.copy_phase_transfers_output_state
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-14T22:28:41.160749+00:00
-- url     : https://prove2.me/submissions/8189d8d1-1ccc-4cb2-b56e-a79a4805d336

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

The transfer phase of the sequential composite of two bundled TM2 machines, with the
internal state pinned as well as the stacks.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiTM2_Composite
import Theorems.Thm_ShiTM_copy_loop_transfers_stack

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing ShiTM2

/-!
# The transfer phase, with the transfer register accounted for

This strengthens `ShiTM.copy_phase_transfers_output`, which described only the stacks after the
two copy passes and left the internal state existentially bound.  That is not enough to chain:

* phase 3 can only be entered at internal state `tm₂.initialState`, because the phase-3
  simulation lemma describes `tm₂` from `Turing.initList tm₂ _`;
* the run must *land* on `Turing.haltList (comp ..) u`, whose `var` field is pinned to
  `compInitialState tm₁ tm₂ = (tm₁.initialState, tm₂.initialState, none)`
  (`Computable.lean:118-123`).

So all three coordinates of the final state are needed, and no extensionality argument recovers
them after the fact.  They are, however, already present in
`ShiTM.copy_loop_transfers_stack`, whose conclusion carries
`var := fpop (s.foldl (fun w y => fpop w (some y)) v) none`.

The content is that both copy passes leave the two machine-state components alone and use only
the register:

* `loadRegA tm₁ tm₂ tr w o = (w.1, w.2.1, o.map tr)`,
* `loadRegB tm₁ tm₂ w o = (w.1, w.2.1, o)`,

so a `foldl` of either preserves `.1` and `.2.1`, and the *exiting* application -- the one on
the failed pop that ends each loop -- is at `o = none`, which empties the register.  Hence the
state after the whole transfer is `(v.1, v.2.1, none)`: unconditionally, with no hypothesis on
`v`.  In the intended instantiation `v = (tm₁.initialState, tm₂.initialState, none)` already,
and this says the transfer preserves it.

## Formulation

`v'` stays existentially bound and the pin is added as a separate conjunct,
`v' = (v.1, v.2.1, Option.none)`, rather than writing the pinned triple directly into the
configuration.  This is not a matter of taste.  Substituting the pinned value into the
configuration would require rewriting the *iterate equation* produced by the platform lemma,
and the type of that hypothesis mentions a `CompΓ`-indexed `List.map`, which is type-correct
only at default transparency; `rw`/`simp` re-elaborate the hypothesis they traverse at
`implicit` transparency and so fail before rewriting anything (see the transparency taxonomy
below).  Keeping the pin as its own conjunct means the register fact is proved on a goal that
mentions only `Compσ tm₁ tm₂ = tm₁.σ × tm₂.σ × Option (tm₂.Γ tm₂.k₀)` -- no `Sum.elim`
anywhere -- and the iterate equations are never touched.  A caller does
`obtain ⟨v', S', h₁, h₂, …, hv⟩` and `subst hv`.

Everything else -- the per-key stack conclusions and the exact `2 * s.length + 2` step count --
is unchanged from `copy_phase_transfers_output`.
-/

/-!
## The `Sum.elim` transparency taxonomy

`CompΓ tm₁ tm₂ (injK₁ tm₁ tm₂ i)` and `tm₁.Γ i` are equal by `rfl`, but `CompΓ` is a `Sum.elim`
and `Sum.elim` is semireducible, so only *default* transparency sees the equation.  Three
distinct things break, each needing a different answer:

1. **Application checking** (`List.map tr (S (injK₁ ..))`) runs at `implicit` transparency.
   Fixed by ascribing **`tr` itself**, not the resulting list: that reruns the check at default
   transparency and makes `List.map`'s implicit type arguments come out as `CompΓ ..`, the form
   `copy_loop_transfers_stack` produces from its own `e : Γ ka → Γ kb`, so terms match
   syntactically rather than merely up to defeq.
2. **Instance synthesis** (`_ ++ S (injK₂ ..)`) cannot be steered from the operands at all:
   expected-type propagation beats an ascription on either side, and typeclass search is
   hardcoded to `instances` transparency.  Fixed by keeping `++` out of statements; `hin`
   absorbs it.
3. **Rewriting a hypothesis.**  `rw .. at h`/`simp .. at h` re-elaborate `h`'s type at
   `implicit` transparency and choke before rewriting.  Fixed by never creating such a
   hypothesis: pass B is instantiated at an opaque local `sB` introduced by `obtain`, and every
   bridge is applied on the *goal* or by `exact`.

There is no `rw .. at` or `simp .. at` anywhere in this file.

Note also that everything is stated at `ShiTM2.compM tm₁ tm₂ tr dflt` and never at
`(ShiTM2.comp tm₁ tm₂ tr dflt).step`.  `Turing.FinTM2.step tm = Turing.TM2.step tm.m` needs
`[DecidableEq tm.K]`, and at `comp ..` typeclass synthesis finds
`Turing.FinTM2.decidableEqK (comp ..)` (`Computable.lean:80`), which reduces to
`ShiTM2.compKDecEq tm₁ tm₂` and is *not* defeq to the free variable supplied by a
`[DecidableEq (CompK tm₁ tm₂)]` binder.  Staying at `compM` avoids the clash entirely.
-/

/-! ### Pairwise distinctness of the three stack indices in play

`injK₁ _ = Sum.inl _`, `injK₂ _ = Sum.inr (Sum.inl _)` and `kScr = Sum.inr (Sum.inr ())`, so
each pair differs by a constructor. -/

/-- `tm₁`'s output stack is not the scratch stack. -/
private lemma shiXfer2_ne_k₁_scr (tm₁ tm₂ : Turing.FinTM2) :
    ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁ ≠ ShiTM2.kScr tm₁ tm₂ := by
  first
    | (exact Sum.inl_ne_inr; done)
    | (intro h; exact Sum.noConfusion h; done)
    | (simp [ShiTM2.injK₁, ShiTM2.kScr]; done)

/-- The scratch stack is not `tm₂`'s input stack. -/
private lemma shiXfer2_ne_scr_k₀ (tm₁ tm₂ : Turing.FinTM2) :
    ShiTM2.kScr tm₁ tm₂ ≠ ShiTM2.injK₂ tm₁ tm₂ tm₂.k₀ := by
  first
    | (intro h; exact Sum.inr_ne_inl (Sum.inr.inj h); done)
    | (intro h; injection h with h'; exact Sum.inr_ne_inl h'; done)
    | (simp [ShiTM2.kScr, ShiTM2.injK₂]; done)

/-- `tm₁`'s output stack is not `tm₂`'s input stack. -/
private lemma shiXfer2_ne_k₁_k₀ (tm₁ tm₂ : Turing.FinTM2) :
    ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁ ≠ ShiTM2.injK₂ tm₁ tm₂ tm₂.k₀ := by
  first
    | (exact Sum.inl_ne_inr; done)
    | (intro h; exact Sum.noConfusion h; done)
    | (simp [ShiTM2.injK₁, ShiTM2.injK₂]; done)

/-! ### Generic list helpers

Stated at generic `Type`s -- where no `Sum.elim` is in scope, so the `rw`s inside are purely
syntactic -- and applied with `exact`, which discharges the `CompΓ` opacity with one defeq
check at default transparency. -/

/-- One pop/push pass reverses; two do not. -/
private lemma shiXfer2_map_id_reverse {α : Type} (l : List α) :
    ((l.reverse).map (id : α → α)).reverse = l := by
  rw [List.map_id, List.reverse_reverse]

/-- Pass B runs for as many steps as pass A. -/
private lemma shiXfer2_length_map_reverse {α β : Type} (l : List α) (f : α → β) :
    ((l.map f).reverse).length = l.length := by
  rw [List.length_reverse, List.length_map]

/-- Collapse the `++ S kb` that the platform lemma produces, given that `S kb` was empty. -/
private lemma shiXfer2_append_nil_eq {α : Type} {l m n : List α} (hm : m = []) (h : l = n) :
    l ++ m = n := by
  rw [hm, List.append_nil]
  exact h

/-! ### The register invariant

Both copy passes step the internal state by a function of the form
`fun w y => (w.1, w.2.1, g y)`, which touches only the third component.  The two generic
lemmas below say a `foldl` of such a step preserves the first two components; the two
specialised wrappers then read off the state after the *exiting* application, which is at
`o = none`.

The wrappers are stated in terms of `ShiTM2.loadRegA`/`loadRegB`, whose own signatures mention
`tm₁.Γ tm₁.k₁` and `tm₂.Γ tm₂.k₀` and never `CompΓ`, so they too are free of the `Sum.elim`
opacity.  At the use site the platform lemma's `foldl` ranges over `List (CompΓ ..)`; that is
reconciled by the single defeq check `exact` performs. -/

/-- A `foldl` that only ever rewrites the third component preserves the first. -/
private lemma shiXfer2_foldl_fst {α A B C : Type} (g : α → C) :
    ∀ (l : List α) (w : A × B × C),
      (l.foldl (fun u y => (u.1, u.2.1, g y)) w).1 = w.1 := by
  intro l
  induction l with
  | nil =>
      intro w
      rfl
  | cons a t ih =>
      intro w
      exact ih (w.1, w.2.1, g a)

/-- A `foldl` that only ever rewrites the third component preserves the second. -/
private lemma shiXfer2_foldl_snd_fst {α A B C : Type} (g : α → C) :
    ∀ (l : List α) (w : A × B × C),
      (l.foldl (fun u y => (u.1, u.2.1, g y)) w).2.1 = w.2.1 := by
  intro l
  induction l with
  | nil =>
      intro w
      rfl
  | cons a t ih =>
      intro w
      exact ih (w.1, w.2.1, g a)

/-- The state after a whole copy loop, with the register emptied by the exiting failed pop. -/
private lemma shiXfer2_foldl_reg {α A B C : Type} (g : α → C) (z : C) (l : List α)
    (w : A × B × C) :
    ((l.foldl (fun u y => (u.1, u.2.1, g y)) w).1,
      (l.foldl (fun u y => (u.1, u.2.1, g y)) w).2.1, z) = (w.1, w.2.1, z) := by
  rw [shiXfer2_foldl_fst g l w, shiXfer2_foldl_snd_fst g l w]

/-- Pass A empties the register and leaves both machine states alone. -/
private lemma shiXfer2_loadRegA_foldl (tm₁ tm₂ : Turing.FinTM2)
    (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀) (w : ShiTM2.Compσ tm₁ tm₂)
    (l : List (tm₁.Γ tm₁.k₁)) :
    ShiTM2.loadRegA tm₁ tm₂ tr
        (l.foldl (fun u y => ShiTM2.loadRegA tm₁ tm₂ tr u (some y)) w) none
      = (w.1, w.2.1, Option.none) := by
  first
    | (exact shiXfer2_foldl_reg (fun y => Option.map tr (some y)) Option.none l w; done)
    | (exact shiXfer2_foldl_reg (fun y => Option.some (tr y)) Option.none l w; done)

/-- Pass B empties the register and leaves both machine states alone. -/
private lemma shiXfer2_loadRegB_foldl (tm₁ tm₂ : Turing.FinTM2)
    (w : ShiTM2.Compσ tm₁ tm₂) (l : List (tm₂.Γ tm₂.k₀)) :
    ShiTM2.loadRegB tm₁ tm₂
        (l.foldl (fun u y => ShiTM2.loadRegB tm₁ tm₂ u (some y)) w) none
      = (w.1, w.2.1, Option.none) := by
  first
    | (exact shiXfer2_foldl_reg Option.some Option.none l w; done)
    | (exact shiXfer2_foldl_reg (fun y => Option.some y) Option.none l w; done)

/-! ### The transfer phase -/

/-- **The transfer phase runs in exactly `2 * s.length + 2` steps, moves `tm₁`'s output onto
`tm₂`'s input without reversing it, and returns the internal state to `(v.1, v.2.1, none)`.**

Starting from the copy-pass-A entry label `lcopyA` with internal state `v` and stacks `S` whose
scratch stack and `tm₂`-input stack are both empty, `ShiTM2.compM tm₁ tm₂ tr dflt` reaches the
second machine's entry label `injΛ₂ tm₂.main` in exactly `2 * s.length + 2` steps, where
`s = S (injK₁ tm₁ tm₂ tm₁.k₁)` is `tm₁`'s output stack.  Afterwards:

* `tm₂`'s input stack holds `s.map tr`, in the original order -- the two pop/push reversals
  cancel;
* `tm₁`'s output stack and the scratch stack are empty, and no other stack has changed;
* the internal state is `(v.1, v.2.1, none)`: both machine-state components are exactly as
  they were, and the transfer register is empty.

The last item is what lets phase 3 be entered at `tm₂.initialState` and the run land on
`Turing.haltList`, whose `var` is pinned to `compInitialState tm₁ tm₂`. -/
theorem solution (tm₁ tm₂ : Turing.FinTM2) [DecidableEq (ShiTM2.CompK tm₁ tm₂)]
    (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀) (dflt : tm₂.Γ tm₂.k₀)
    (v : ShiTM2.Compσ tm₁ tm₂) (S : ∀ k, List (ShiTM2.CompΓ tm₁ tm₂ k))
    (hscr : S (ShiTM2.kScr tm₁ tm₂) = [])
    (hin : S (ShiTM2.injK₂ tm₁ tm₂ tm₂.k₀) = []) :
    ∃ (v' : ShiTM2.Compσ tm₁ tm₂) (S' : ∀ k, List (ShiTM2.CompΓ tm₁ tm₂ k)),
      (fun c : Option (ShiTM2.CompCfg tm₁ tm₂) =>
            c.bind (Turing.TM2.step (ShiTM2.compM tm₁ tm₂ tr dflt)))^[
          2 * (S (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)).length + 2]
            (some { l := some (ShiTM2.lcopyA tm₁ tm₂), var := v, stk := S })
          = some { l := some (ShiTM2.injΛ₂ tm₁ tm₂ tm₂.main), var := v', stk := S' }
      ∧ Nonempty (StateTransition.EvalsToInTime
            (Turing.TM2.step (ShiTM2.compM tm₁ tm₂ tr dflt))
            { l := some (ShiTM2.lcopyA tm₁ tm₂), var := v, stk := S }
            (some { l := some (ShiTM2.injΛ₂ tm₁ tm₂ tm₂.main), var := v', stk := S' })
            (2 * (S (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)).length + 2))
      ∧ S' (ShiTM2.injK₂ tm₁ tm₂ tm₂.k₀)
          = (S (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)).map
              (tr : ShiTM2.CompΓ tm₁ tm₂ (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁) →
                    ShiTM2.CompΓ tm₁ tm₂ (ShiTM2.injK₂ tm₁ tm₂ tm₂.k₀))
      ∧ S' (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁) = []
      ∧ S' (ShiTM2.kScr tm₁ tm₂) = []
      ∧ (∀ k, k ≠ ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁ → k ≠ ShiTM2.injK₂ tm₁ tm₂ tm₂.k₀ →
          k ≠ ShiTM2.kScr tm₁ tm₂ → S' k = S k)
      ∧ v' = (v.1, v.2.1, Option.none) := by
  -- Pass A: `injK₁ tm₁.k₁` onto the scratch stack, translating along `tr`.
  have hA : ∃ (vA : ShiTM2.Compσ tm₁ tm₂) (SA : ∀ k, List (ShiTM2.CompΓ tm₁ tm₂ k)),
      (fun c : Option (ShiTM2.CompCfg tm₁ tm₂) =>
            c.bind (Turing.TM2.step (ShiTM2.compM tm₁ tm₂ tr dflt)))^[
          (S (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)).length + 1]
            (some { l := some (ShiTM2.lcopyA tm₁ tm₂), var := v, stk := S })
          = some { l := some (ShiTM2.lcopyB tm₁ tm₂), var := vA, stk := SA }
      ∧ Nonempty (StateTransition.EvalsToInTime
            (Turing.TM2.step (ShiTM2.compM tm₁ tm₂ tr dflt))
            { l := some (ShiTM2.lcopyA tm₁ tm₂), var := v, stk := S }
            (some { l := some (ShiTM2.lcopyB tm₁ tm₂), var := vA, stk := SA })
            ((S (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)).length + 1))
      ∧ SA (ShiTM2.kScr tm₁ tm₂)
          = ((S (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)).map
              (tr : ShiTM2.CompΓ tm₁ tm₂ (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁) →
                    ShiTM2.CompΓ tm₁ tm₂ (ShiTM2.kScr tm₁ tm₂))).reverse
      ∧ SA (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁) = []
      ∧ (∀ k, k ≠ ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁ → k ≠ ShiTM2.kScr tm₁ tm₂ → SA k = S k)
      ∧ vA = (v.1, v.2.1, Option.none) := by
    obtain ⟨hIter, hEv⟩ :=
      ShiTM.copy_loop_transfers_stack (ShiTM2.compM tm₁ tm₂ tr dflt)
        (ka := ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁) (kb := ShiTM2.kScr tm₁ tm₂)
        (shiXfer2_ne_k₁_scr tm₁ tm₂)
        (lc := ShiTM2.lcopyA tm₁ tm₂) (lnext := ShiTM2.lcopyB tm₁ tm₂)
        (fpop := ShiTM2.loadRegA tm₁ tm₂ tr) (gtest := ShiTM2.regIsSome tm₁ tm₂)
        (hpush := ShiTM2.pushReg tm₁ tm₂ dflt) (e := tr)
        rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
        (S (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)) v S rfl
    refine ⟨_, _, hIter, hEv, ?_, ?_, ?_, ?_⟩
    · exact (Function.update_self _ _ _).trans (shiXfer2_append_nil_eq hscr rfl)
    · exact (Function.update_of_ne (shiXfer2_ne_k₁_scr tm₁ tm₂) _ _).trans
        (Function.update_self _ _ _)
    · intro k hk₁ hkscr
      exact (Function.update_of_ne hkscr _ _).trans (Function.update_of_ne hk₁ _ _)
    · exact shiXfer2_loadRegA_foldl tm₁ tm₂ tr v _
  obtain ⟨vA, SA, hIterA, hEvA, hSAscr, hSAk₁, hSAoth, hvA⟩ := hA
  -- `tm₂`'s input stack is untouched by pass A, hence still empty.
  have hSAk₀ : SA (ShiTM2.injK₂ tm₁ tm₂ tm₂.k₀) = [] :=
    (hSAoth (ShiTM2.injK₂ tm₁ tm₂ tm₂.k₀) (shiXfer2_ne_k₁_k₀ tm₁ tm₂).symm
      (shiXfer2_ne_scr_k₀ tm₁ tm₂).symm).trans hin
  -- Make pass B's input list an OPAQUE LOCAL before instantiating, so that no hypothesis whose
  -- type mentions a `CompΓ`-indexed `List.map` ever has to be traversed by a tactic.
  obtain ⟨sB, hsB, hsBlen, hsBrev⟩ :
      ∃ sB : List (ShiTM2.CompΓ tm₁ tm₂ (ShiTM2.kScr tm₁ tm₂)),
        SA (ShiTM2.kScr tm₁ tm₂) = sB
        ∧ sB.length = (S (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)).length
        ∧ (sB.map (id : ShiTM2.CompΓ tm₁ tm₂ (ShiTM2.kScr tm₁ tm₂) →
              ShiTM2.CompΓ tm₁ tm₂ (ShiTM2.injK₂ tm₁ tm₂ tm₂.k₀))).reverse
            = (S (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)).map
                (tr : ShiTM2.CompΓ tm₁ tm₂ (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁) →
                      ShiTM2.CompΓ tm₁ tm₂ (ShiTM2.injK₂ tm₁ tm₂ tm₂.k₀)) :=
    ⟨((S (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)).map
        (tr : ShiTM2.CompΓ tm₁ tm₂ (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁) →
              ShiTM2.CompΓ tm₁ tm₂ (ShiTM2.kScr tm₁ tm₂))).reverse,
      hSAscr,
      shiXfer2_length_map_reverse _ _,
      shiXfer2_map_id_reverse _⟩
  -- Pass B: the scratch stack onto `injK₂ tm₂.k₀`, undoing pass A's reversal.
  have hB : ∃ (vB : ShiTM2.Compσ tm₁ tm₂) (SB : ∀ k, List (ShiTM2.CompΓ tm₁ tm₂ k)),
      (fun c : Option (ShiTM2.CompCfg tm₁ tm₂) =>
            c.bind (Turing.TM2.step (ShiTM2.compM tm₁ tm₂ tr dflt)))^[sB.length + 1]
            (some { l := some (ShiTM2.lcopyB tm₁ tm₂), var := vA, stk := SA })
          = some { l := some (ShiTM2.injΛ₂ tm₁ tm₂ tm₂.main), var := vB, stk := SB }
      ∧ Nonempty (StateTransition.EvalsToInTime
            (Turing.TM2.step (ShiTM2.compM tm₁ tm₂ tr dflt))
            { l := some (ShiTM2.lcopyB tm₁ tm₂), var := vA, stk := SA }
            (some { l := some (ShiTM2.injΛ₂ tm₁ tm₂ tm₂.main), var := vB, stk := SB })
            (sB.length + 1))
      ∧ SB (ShiTM2.injK₂ tm₁ tm₂ tm₂.k₀)
          = (S (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)).map
              (tr : ShiTM2.CompΓ tm₁ tm₂ (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁) →
                    ShiTM2.CompΓ tm₁ tm₂ (ShiTM2.injK₂ tm₁ tm₂ tm₂.k₀))
      ∧ SB (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁) = []
      ∧ SB (ShiTM2.kScr tm₁ tm₂) = []
      ∧ (∀ k, k ≠ ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁ → k ≠ ShiTM2.injK₂ tm₁ tm₂ tm₂.k₀ →
          k ≠ ShiTM2.kScr tm₁ tm₂ → SB k = S k)
      ∧ vB = (v.1, v.2.1, Option.none) := by
    obtain ⟨hIter, hEv⟩ :=
      ShiTM.copy_loop_transfers_stack (ShiTM2.compM tm₁ tm₂ tr dflt)
        (ka := ShiTM2.kScr tm₁ tm₂) (kb := ShiTM2.injK₂ tm₁ tm₂ tm₂.k₀)
        (shiXfer2_ne_scr_k₀ tm₁ tm₂)
        (lc := ShiTM2.lcopyB tm₁ tm₂) (lnext := ShiTM2.injΛ₂ tm₁ tm₂ tm₂.main)
        (fpop := ShiTM2.loadRegB tm₁ tm₂) (gtest := ShiTM2.regIsSome tm₁ tm₂)
        (hpush := ShiTM2.pushReg tm₁ tm₂ dflt) (e := id)
        rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
        sB vA SA hsB
    -- Pure `Eq.trans` chains only.
    refine ⟨_, _, hIter, hEv, ?_, ?_, ?_, ?_, ?_⟩
    · exact (Function.update_self _ _ _).trans (shiXfer2_append_nil_eq hSAk₀ hsBrev)
    · exact (Function.update_of_ne (shiXfer2_ne_k₁_k₀ tm₁ tm₂) _ _).trans
        ((Function.update_of_ne (shiXfer2_ne_k₁_scr tm₁ tm₂) _ _).trans hSAk₁)
    · exact (Function.update_of_ne (shiXfer2_ne_scr_k₀ tm₁ tm₂) _ _).trans
        (Function.update_self _ _ _)
    · intro k hk₁ hk₀ hkscr
      exact (Function.update_of_ne hk₀ _ _).trans
        ((Function.update_of_ne hkscr _ _).trans (hSAoth k hk₁ hkscr))
    · refine (shiXfer2_loadRegB_foldl tm₁ tm₂ vA _).trans ?_
      first
        | (rw [hvA]; done)
        | (rw [hvA]; rfl; done)
        | (rw [hvA]; exact rfl; done)
  obtain ⟨vB, SB, hIterB, hEvB, hSBk₀, hSBk₁, hSBscr, hSBoth, hvB⟩ := hB
  -- The single arithmetic bridge, used by BOTH chainings.  `EvalsToInTime.trans` is indexed by
  -- `m₂ + m₁`, with pass B's bound on the left, so the sum is written in that order; `omega`
  -- closes it from `hsBlen` in context.  This is a rewrite on the GOAL, whose type mentions
  -- only the opaque locals `vB`/`SB`, never a `CompΓ`-indexed `List.map`.
  have harith : 2 * (S (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)).length + 2
      = (sB.length + 1) + ((S (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)).length + 1) := by
    first
      | (omega; done)
      | (rw [hsBlen]; omega; done)
      | (rw [hsBlen]; ring_nf; done)
  -- Chain the two iterate equations.
  have hcomb : (fun c : Option (ShiTM2.CompCfg tm₁ tm₂) =>
        c.bind (Turing.TM2.step (ShiTM2.compM tm₁ tm₂ tr dflt)))^[
      2 * (S (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)).length + 2]
        (some { l := some (ShiTM2.lcopyA tm₁ tm₂), var := v, stk := S })
      = some { l := some (ShiTM2.injΛ₂ tm₁ tm₂ tm₂.main), var := vB, stk := SB } := by
    rw [harith, Function.iterate_add_apply, hIterA, hIterB]
  refine ⟨vB, SB, hcomb, ?_, hSBk₀, hSBk₁, hSBscr, hSBoth, hvB⟩
  -- Chain the two `EvalsToInTime` witnesses.  `EvalsToInTime.trans` is a `def` landing in
  -- `Type`, so destructure both `Nonempty`s and re-wrap; the target `Nonempty _` is a `Prop`,
  -- so the elimination is allowed.  The intermediate configuration is given explicitly rather
  -- than left to unify `↑b` against `some cfg`.
  obtain ⟨eA⟩ := hEvA
  obtain ⟨eB⟩ := hEvB
  rw [harith]
  first
    | (exact ⟨StateTransition.EvalsToInTime.trans
          (Turing.TM2.step (ShiTM2.compM tm₁ tm₂ tr dflt))
          ((S (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)).length + 1)
          (sB.length + 1)
          { l := some (ShiTM2.lcopyA tm₁ tm₂), var := v, stk := S }
          { l := some (ShiTM2.lcopyB tm₁ tm₂), var := vA, stk := SA }
          (some { l := some (ShiTM2.injΛ₂ tm₁ tm₂ tm₂.main), var := vB, stk := SB })
          eA eB⟩
       done)
    | (exact ⟨StateTransition.EvalsToInTime.trans _ _ _ _ _ _ eA eB⟩; done)
    | (refine ⟨StateTransition.EvalsToInTime.trans _ _ _ _
          { l := some (ShiTM2.lcopyB tm₁ tm₂), var := vA, stk := SA } _ eA eB⟩
       done)
