-- Prove2me | solution 1 for ShiTM.comp_outputsInTime
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-15T00:07:25.434056+00:00
-- url     : https://prove2.me/submissions/a8e9f96b-d072-431e-bb5d-30b00dae66bc

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

The sequential composite of two bundled TM2 machines outputs the composition.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiTM2_Composite
import Theorems.Thm_ShiTM_initList_haltList_laws
import Theorems.Thm_ShiTM_initList_haltList_comp
import Theorems.Thm_ShiTM_iterate_compM_one_simulation
import Theorems.Thm_ShiTM_iterate_compM_two_simulation
import Theorems.Thm_ShiTM_copy_phase_transfers_output_state

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing ShiTM2

/-!
# The composite machine outputs the composition

`ShiTM2.comp tm1 tm2 tr dflt` (`Definitions/Def_ShiTM2_Composite.lean`) runs `tm1` on its input
stack, moves `tm1`'s output stack onto `tm2`'s input stack through a scratch stack, and then runs
`tm2`.  This file is the **chaining**: if `tm1` outputs `t` on `s` within `m1` steps and `tm2`
outputs `u` on `t.map tr` within `m2` steps, then the composite outputs `u` on `s` within
`m1 + (2 * t.length + 2) + m2` steps.  No polynomial arithmetic and no
`Turing.TM2ComputableInPolyTime` structure is built here; both are separate.

The run is assembled from three accepted platform theorems, one per phase, plus the two
configuration-law bundles:

1. `ShiTM.iterate_compM_one_simulation` -- phase 1, step-exact, `N1` steps;
2. `ShiTM.copy_phase_transfers_output_state` -- phase 2, exactly `2 * t.length + 2` steps;
3. `ShiTM.iterate_compM_two_simulation` -- phase 3, step-exact, `N2` steps.

`N1` and `N2` are the *actual* step counts recorded in the `StateTransition.EvalsTo.steps` fields
of the two hypotheses, not the bounds `m1`/`m2`; the bounds re-enter only at the very end through
`steps_le_m`.

## What is not supplied by any ingredient, and had to be proved here

Both iteration lemmas require `hlive`: the simulated component has not halted at any `j < n`.
`Turing.TM2OutputsInTime` does not give this.  `shiAsm_no_early_death` derives it.  The argument
is: a `none` state is a fixed point of the one-step map on `Option`, so if the `j`-th iterate were
`none`, or were `some` of a configuration with label `none` (in which case the `(j+1)`-st iterate
is `none`, because `Turing.TM2.step` of a halted configuration is `none`), then every later
iterate -- in particular the `n`-th -- would be `none`, contradicting that the `n`-th iterate is
`some`.  Persistence needs no `Nat.le_induction`: from `i <= n` write `n = d + i` with `d` obtained
*opaquely*, and `Function.iterate_add_apply` plus `shiAsm_iterate_none` finish it.

One statement serves **both** phases: it never constrains the final configuration's label, so
phase 3's "the component may halt at the last step" needs no separate version.

## The three configuration matchings

All three are `Turing.TM2.Cfg` extensionality (`shiAsm_cfg_ext`: three field equalities, `funext`
on `stk`, and Lean 4 structure eta for `c = <c.l, c.var, c.stk>`).  Nothing deeper was needed.

* **Entry.**  `Turing.initList (comp ..) s` is the `liftCfg1`-lift of `Turing.initList tm1 s`
  against the empty background.  `l`: `Option.elim` on `some tm1.main` is iota.  `var`:
  `ShiTM2.compInitialState` *is* `(tm1.initialState, tm2.initialState, none)`, so the `liftCfg1`
  state `(c.var, tm2.initialState, none)` matches on the nose.  `stk`: the three per-key facts of
  `ShiTM.initList_haltList_comp`.
* **Phase 1 to phase 2 (the halt redirection).**  `Turing.haltList tm1 t` has label `none`, and
  `liftCfg1` sends `none` to the *live* label `lcopyA` -- which is why phase 2 can start at all.
  Only the `l` field needs an argument; `var` and `stk` are taken as projections of the very
  configuration being rewritten, hence `rfl`.
* **Phase 2 to phase 3, and phase 3 to `haltList`.**  The register conjunct
  `v' = (v.1, v.2.1, none)` of `ShiTM.copy_phase_transfers_output_state` is what pins all three
  coordinates of the internal state: phase 3 cannot *start* without `v'.2.1 = tm2.initialState`
  (its start state must be `Turing.initList tm2 (t.map tr)`'s, namely `tm2.initialState`), and it
  cannot *land* on `Turing.haltList (comp ..) u` without `v'.1 = tm1.initialState` and
  `v'.2.2 = none`, since `Turing.haltList` pins the final state to `(comp ..).initialState`.
  The weaker `ShiTM.copy_phase_transfers_output`, whose `v'` is unconstrained, does not chain.

## The two transparency hazards, and how each is answered

`ShiTM2.CompGamma tm1 tm2 (injK1 .. i)` is `tm1.Gamma i` by `rfl`, but only at *default*
transparency, because `CompGamma` is a reducible `abbrev` over a semireducible `Sum.elim`.

1. **No rewriting tactic ever traverses a hypothesis whose type mentions a `CompGamma`-indexed
   `List.map`.**  The transfer conclusion `S' (injK2 .. tm2.k0) = (Sm (injK1 .. tm1.k1)).map tr` is
   consumed only by `Eq.trans` and `congrArg`, and the arithmetic bridge
   `(Sm (injK1 .. tm1.k1)).length = t.length` is applied on the *goal*.  Both `Sm` and `S'` are
   opaque locals introduced by `obtain` from an existential, so every hypothesis stated about them
   is `CompGamma`-free in the dangerous position.  There is no `++` anywhere in this file.
2. **No dependent function is ever handed across the two spellings.**  `ShiTM2.liftStk1` is never
   applied by hand -- the stack family is always taken as `(ShiTM2.liftCfg1 ..).stk`, a projection
   -- so the application check that would compare `forall k, List (tm1.Gamma k)` against
   `forall i, List (CompGamma .. (injK1 .. i))` never runs.

## Why the conclusion is `Nonempty`

`StateTransition.EvalsToInTime` (`Computability/StateTransition.lean:265`) is a structure in
`Type`, not a `Prop`: it *carries* the step count.  So `Turing.TM2OutputsInTime` is data, a
`theorem` cannot return it, and -- the knock-on -- no `∃` could be destructured while the goal
was `Type`-valued (`Exists.casesOn` eliminates only into `Prop`).  Wrapping the conclusion in
`Nonempty` fixes both at once, and loses nothing: the eventual target is itself `Nonempty`
(`PvsNP.PolyTimeComputable f := Nonempty (TM2ComputableInPolyTime id id f)`,
`Definitions/Def_PvsNP.lean:71`), so a later file recovers the data with `Classical.choice`
exactly as Mathlib's own `idComputableInPolyTime` does inside a `noncomputable section`.

## `noConfusion` is unusable here; the named `_ne_` lemmas are not

`Option.noConfusion` and `Sum.noConfusion` want their motive at `Sort (u + 2)`, and
`CompK tm₁ tm₂`, `tm₁.Λ` and friends all sit in `Type 0`, so the universe constraint is
unsatisfiable.  `Option.some_ne_none` (`Init/Data/Option/Lemmas.lean:31`), `Sum.inl_ne_inr`
(`Init/Data/Sum/Lemmas.lean:103`) and `Sum.inr_ne_inl` (`:105`) are all `nofun` and carry no
such constraint.

## The instance mismatch at the final `exact`

`Turing.TM2OutputsInTime (comp ..) ..` unfolds to `StateTransition.EvalsToInTime (comp ..).step ..`,
and `(comp ..).step` carries `Turing.FinTM2.decidableEqK (comp ..)`
(`Computability/TuringMachine/Computable.lean:80`, an honest `instance`).  Every accepted
ingredient instead carries the *free variable* `inst` of the `[DecidableEq (CompK tm1 tm2)]`
binder, and an `fvar` is not definitionally equal to `decidableEqK (comp ..)`, so the closing
`exact` fails and `show` cannot repair it.  `shiAsm_decEq_unique` (decidable equality is a
subsingleton, `funext` plus core's `Subsingleton (Decidable p)`) gives the propositional equality,
and `subst` then retypes every derived hypothesis without re-elaborating any of them -- which is
also why `subst`, and not `rw .. at`, is the right tool given hazard 1 above.
-/

/-! ### Configuration extensionality

Three field equalities determine a `Turing.TM2.Cfg`.  Stated at generic types, where no
`Sum.elim` is in scope, and applied by `refine`/`exact`, which check at default transparency. -/

/-- Two `TM2` configurations agreeing field- and key-wise are equal. -/
private lemma shiAsm_cfg_ext {K : Type} {Γ : K → Type} {Λ σ : Type}
    {c d : Turing.TM2.Cfg Γ Λ σ} (hl : c.l = d.l) (hv : c.var = d.var)
    (hs : ∀ k, c.stk k = d.stk k) : c = d := by
  have hs' : c.stk = d.stk := funext hs
  have h1 : c = (Turing.TM2.Cfg.mk c.l c.var c.stk : Turing.TM2.Cfg Γ Λ σ) := rfl
  have h2 : d = (Turing.TM2.Cfg.mk d.l d.var d.stk : Turing.TM2.Cfg Γ Λ σ) := rfl
  first
    | (rw [h1, h2, hl, hv, hs']
       done)
    | (refine h1.trans ?_
       rw [hl, hv, hs']
       exact h2.symm
       done)
    | (refine h1.trans (Eq.trans ?_ h2.symm)
       rw [hl, hv, hs']
       done)

/-! ### `none` is a fixed point of the one-step map

`Turing.TM2.step` of a halted configuration is `none` (`StackTuringMachine.lean:171-173`) and a
`none` state cannot be revived, so a machine that is dead at step `j` is dead at every later step.
This is what refutes the two bad branches of `shiAsm_no_early_death`. -/

/-- Every iterate of the one-step map fixes `none`. -/
private lemma shiAsm_iterate_none {σ : Type} (f : σ → Option σ) (n : ℕ) :
    (fun c : Option σ => c.bind f)^[n] (Option.none : Option σ) = Option.none := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    first
      | (rw [Function.iterate_succ_apply]
         exact ih
         done)
      | (simp only [Function.iterate_succ_apply, Option.bind_none]
         exact ih
         done)

/-- **No early death.**  If `n` steps carry the live configuration `<some l, v, S>` to *some*
configuration, then at every intermediate time `j < n` the machine is still live: the `j`-th
iterate is `some` of a configuration whose label is `some`.

This is exactly the `hlive` hypothesis that `ShiTM.iterate_compM_one_simulation` and
`ShiTM.iterate_compM_two_simulation` demand and that `Turing.TM2OutputsInTime` does not supply.
The conclusion says nothing about the final configuration `c`, so the same statement serves
phase 1 (where the component's own halt is redirected) and phase 3 (where the component may halt
at the last step, its halt being the composite's). -/
private lemma shiAsm_no_early_death {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Turing.TM2.Stmt Γ Λ σ) (n : ℕ) (l : Λ) (v : σ)
    (S : ∀ k, List (Γ k)) (c : Turing.TM2.Cfg Γ Λ σ)
    (h : (fun x : Option (Turing.TM2.Cfg Γ Λ σ) => x.bind (Turing.TM2.step M))^[n]
        (Option.some (Turing.TM2.Cfg.mk (Option.some l) v S)) = Option.some c) :
    ∀ j < n, ∃ (l' : Λ) (v' : σ) (S' : ∀ k, List (Γ k)),
        (fun x : Option (Turing.TM2.Cfg Γ Λ σ) => x.bind (Turing.TM2.step M))^[j]
            (Option.some (Turing.TM2.Cfg.mk (Option.some l) v S))
          = Option.some (Turing.TM2.Cfg.mk (Option.some l') v' S') := by
  intro j hj
  have hpers : ∀ i : ℕ, i ≤ n →
      (fun x : Option (Turing.TM2.Cfg Γ Λ σ) => x.bind (Turing.TM2.step M))^[i]
          (Option.some (Turing.TM2.Cfg.mk (Option.some l) v S)) ≠ Option.none := by
    intro i hi hnone
    obtain ⟨d, hd⟩ : ∃ d : ℕ, n = d + i := ⟨n - i, by omega⟩
    rw [hd, Function.iterate_add_apply, hnone, shiAsm_iterate_none] at h
    first
      | (exact Option.some_ne_none c h.symm
         done)
      | (simp at h
         done)
  cases hx : (fun x : Option (Turing.TM2.Cfg Γ Λ σ) => x.bind (Turing.TM2.step M))^[j]
      (Option.some (Turing.TM2.Cfg.mk (Option.some l) v S)) with
  | none =>
    exact absurd hx (hpers j (le_of_lt hj))
  | some c' =>
    obtain ⟨cl, cv, cS⟩ := c'
    cases cl with
    | none =>
      exfalso
      apply hpers (j + 1) (by omega)
      first
        | (rw [Function.iterate_succ_apply', hx]
           done)
        | (rw [Function.iterate_succ_apply', hx]
           rfl
           done)
        | (simp only [Function.iterate_succ_apply', hx, Option.bind_some]
           rfl
           done)
    | some cl =>
      first
        | (exact ⟨cl, cv, cS, rfl⟩
           done)
        | (exact ⟨cl, cv, cS, hx⟩
           done)

/-! ### Decidable equality is a subsingleton

`Turing.FinTM2` carries `kDecidableEq` as a *field*, and `Turing.FinTM2.decidableEqK`
(`Computable.lean:80`) is the instance derived from it; the accepted composite theorems instead
take `[DecidableEq (CompK tm1 tm2)]` as a binder.  The two are propositionally, not
definitionally, equal, and the closing `exact` needs them identified. -/

/-- Any two decidable-equality instances on the same type are equal. -/
private lemma shiAsm_decEq_unique {K : Type} (i j : DecidableEq K) : i = j := by
  funext a b
  exact Subsingleton.elim _ _

/-! ### Distinctness of the composite's three stack blocks

`injK1 i = Sum.inl i`, `injK2 j = Sum.inr (Sum.inl j)` and `kScr = Sum.inr (Sum.inr ())`, so any
two of them differ by a constructor or by their payload. -/

/-- `Sum.inl` and `Sum.inr` are distinct. -/
private lemma shiAsm_ne_inl_inr {A B : Type} (a : A) (b : B) :
    (Sum.inl a : Sum A B) ≠ Sum.inr b := by
  intro hne
  first
    | (exact Sum.inl_ne_inr hne
       done)
    | (simp at hne
       done)

/-- `Sum.inr` and `Sum.inl` are distinct. -/
private lemma shiAsm_ne_inr_inl {A B : Type} (a : A) (b : B) :
    (Sum.inr b : Sum A B) ≠ Sum.inl a := by
  intro hne
  first
    | (exact Sum.inr_ne_inl hne
       done)
    | (simp at hne
       done)

/-- `Sum.inl` is injective. -/
private lemma shiAsm_ne_inl {A B : Type} {a a' : A} (h : a ≠ a') :
    (Sum.inl a : Sum A B) ≠ Sum.inl a' := by
  intro hne
  exact h (Sum.inl.inj hne)

/-- `Sum.inr` is injective. -/
private lemma shiAsm_ne_inr {A B : Type} {b b' : B} (h : b ≠ b') :
    (Sum.inr b : Sum A B) ≠ Sum.inr b' := by
  intro hne
  exact h (Sum.inr.inj hne)

/-! ### The three-phase chaining -/

/--
**The sequential composite of two bundled `TM2` machines outputs the composition of what they
output, in the sum of their running times plus the cost of the transfer.**

If `tm₁` run on `s` outputs `t` within `m₁` steps, and `tm₂` run on `t.map tr` outputs `u` within
`m₂` steps, then `ShiTM2.comp tm₁ tm₂ tr dflt` run on `s` outputs `u` within
`m₁ + (2 * t.length + 2) + m₂` steps.  The middle summand is exact: the transfer phase pops and
pushes each of the `t.length` symbols twice, once per pass over the scratch stack, plus the two
failing pops that end the passes.

This is the correctness half of Mathlib's `proof_wanted Turing.TM2ComputableInPolyTime.comp`
(`Computability/TuringMachine/Computable.lean:284`) for the identity encoding: it says the
exhibited machine really does compute the composition.  The polynomial bound on
`m₁ + (2 * |f a| + 2) + m₂`, which needs `|f a|` to be polynomially bounded, and the assembly of
the `TM2ComputableInPolyTime` structure are separate.

The conclusion is `Nonempty` of the run rather than the run itself because
`Turing.TM2OutputsInTime` unfolds to a structure in `Type` -- it carries the step count -- and a
`theorem` must be a proposition.  This is the shape the downstream target wants anyway:
`PvsNP.PolyTimeComputable` is itself a `Nonempty`.
-/
theorem solution (tm₁ tm₂ : Turing.FinTM2) [inst : DecidableEq (ShiTM2.CompK tm₁ tm₂)]
    (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀) (dflt : tm₂.Γ tm₂.k₀)
    (s : List (tm₁.Γ tm₁.k₀)) (t : List (tm₁.Γ tm₁.k₁)) (u : List (tm₂.Γ tm₂.k₁))
    (m₁ m₂ : ℕ)
    (h₁ : Turing.TM2OutputsInTime tm₁ s (Option.some t) m₁)
    (h₂ : Turing.TM2OutputsInTime tm₂ (t.map tr) (Option.some u) m₂) :
    Nonempty (Turing.TM2OutputsInTime (ShiTM2.comp tm₁ tm₂ tr dflt) s (Option.some u)
      (m₁ + (2 * t.length + 2) + m₂)) := by
  -- The configuration laws at `tm₁`, at `tm₂`, and at the composite.
  obtain ⟨hi1l, hi1v, -, -, hh1l, hh1v, hh1k₁, hh1ne⟩ :=
    ShiTM.initList_haltList_laws tm₁ s t
  obtain ⟨hi2l, hi2v, hi2k₀, hi2ne, hh2l, hh2v, hh2k₁, hh2ne⟩ :=
    ShiTM.initList_haltList_laws tm₂ (t.map tr) u
  obtain ⟨hcil, hciv, -, -, hchl, hchv, hchk₁, hchne, hci1, hci2, hciscr⟩ :=
    ShiTM.initList_haltList_comp tm₁ tm₂ tr dflt s u
  -- The empty background stack family, kept opaque so that no hypothesis about it has to be
  -- re-elaborated later.
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : ∀ k, List (ShiTM2.CompΓ tm₁ tm₂ k), ∀ k, T₀ k = [] :=
    ⟨fun _ => [], fun _ => rfl⟩
  -- `Turing.TM2OutputsInTime` is a `def`; ascription unfolds it and `Option.map` on `some`.
  have h₁' : StateTransition.EvalsToInTime tm₁.step (Turing.initList tm₁ s)
      (Option.some (Turing.haltList tm₁ t)) m₁ := h₁
  have h₂' : StateTransition.EvalsToInTime tm₂.step (Turing.initList tm₂ (t.map tr))
      (Option.some (Turing.haltList tm₂ u)) m₂ := h₂
  obtain ⟨⟨N₁, hev₁⟩, hle₁⟩ := h₁'
  obtain ⟨⟨N₂, hev₂⟩, hle₂⟩ := h₂'
  -- `flip bind f` is the `fun c => c.bind f` spelling the platform lemmas use; the bridge is
  -- definitional, since `Option.bind_none`/`Option.bind_some` are `rfl` in core.
  have e₁ : (fun x : Option (Turing.TM2.Cfg tm₁.Γ tm₁.Λ tm₁.σ) =>
        x.bind (Turing.TM2.step tm₁.m))^[N₁] (Option.some (Turing.initList tm₁ s))
      = Option.some (Turing.haltList tm₁ t) := by
    first
      | (exact hev₁
         done)
      | (simpa only [flip, Turing.FinTM2.step] using hev₁
         done)
      | (simpa only [flip] using hev₁
         done)
  have e₂ : (fun x : Option (Turing.TM2.Cfg tm₂.Γ tm₂.Λ tm₂.σ) =>
        x.bind (Turing.TM2.step tm₂.m))^[N₂] (Option.some (Turing.initList tm₂ (t.map tr)))
      = Option.some (Turing.haltList tm₂ u) := by
    first
      | (exact hev₂
         done)
      | (simpa only [flip, Turing.FinTM2.step] using hev₂
         done)
      | (simpa only [flip] using hev₂
         done)
  -- Both iteration lemmas need the start configuration as an explicit live triple.
  have hc₁ : Turing.initList tm₁ s
      = (⟨Option.some tm₁.main, tm₁.initialState, (Turing.initList tm₁ s).stk⟩ :
          Turing.TM2.Cfg tm₁.Γ tm₁.Λ tm₁.σ) :=
    shiAsm_cfg_ext hi1l hi1v (fun _ => rfl)
  have hc₂ : Turing.initList tm₂ (t.map tr)
      = (⟨Option.some tm₂.main, tm₂.initialState, (Turing.initList tm₂ (t.map tr)).stk⟩ :
          Turing.TM2.Cfg tm₂.Γ tm₂.Λ tm₂.σ) :=
    shiAsm_cfg_ext hi2l hi2v (fun _ => rfl)
  have e₁' : (fun x : Option (Turing.TM2.Cfg tm₁.Γ tm₁.Λ tm₁.σ) =>
        x.bind (Turing.TM2.step tm₁.m))^[N₁]
        (Option.some (⟨Option.some tm₁.main, tm₁.initialState,
          (Turing.initList tm₁ s).stk⟩ : Turing.TM2.Cfg tm₁.Γ tm₁.Λ tm₁.σ))
      = Option.some (Turing.haltList tm₁ t) := by
    first
      | (rw [← hc₁]
         exact e₁
         done)
      | (exact hc₁ ▸ e₁
         done)
  have e₂' : (fun x : Option (Turing.TM2.Cfg tm₂.Γ tm₂.Λ tm₂.σ) =>
        x.bind (Turing.TM2.step tm₂.m))^[N₂]
        (Option.some (⟨Option.some tm₂.main, tm₂.initialState,
          (Turing.initList tm₂ (t.map tr)).stk⟩ : Turing.TM2.Cfg tm₂.Γ tm₂.Λ tm₂.σ))
      = Option.some (Turing.haltList tm₂ u) := by
    first
      | (rw [← hc₂]
         exact e₂
         done)
      | (exact hc₂ ▸ e₂
         done)
  -- The one thing no ingredient supplies.
  have hlive₁ := shiAsm_no_early_death tm₁.m N₁ tm₁.main tm₁.initialState
    (Turing.initList tm₁ s).stk (Turing.haltList tm₁ t) e₁'
  have hlive₂ := shiAsm_no_early_death tm₂.m N₂ tm₂.main tm₂.initialState
    (Turing.initList tm₂ (t.map tr)).stk (Turing.haltList tm₂ u) e₂'
  -- **Entry.**  The composite's initial configuration is the `liftCfg₁`-lift of `tm₁`'s.
  have hA : Turing.initList (ShiTM2.comp tm₁ tm₂ tr dflt) s
      = ShiTM2.liftCfg₁ tm₁ tm₂ T₀ tm₂.initialState Option.none
          (⟨Option.some tm₁.main, tm₁.initialState, (Turing.initList tm₁ s).stk⟩ :
            Turing.TM2.Cfg tm₁.Γ tm₁.Λ tm₁.σ) := by
    refine shiAsm_cfg_ext hcil hciv ?_
    intro k
    rcases k with i | j | w
    · exact hci1 i
    · exact (hci2 j).trans (hT₀ (ShiTM2.injK₂ tm₁ tm₂ j)).symm
    · first
        | (exact hciscr.trans (hT₀ (ShiTM2.kScr tm₁ tm₂)).symm
           done)
        | (cases w
           exact hciscr.trans (hT₀ (ShiTM2.kScr tm₁ tm₂)).symm
           done)
  -- **Phase 1.**
  obtain ⟨hP1, -⟩ := ShiTM.iterate_compM_one_simulation tm₁ tm₂ tr dflt T₀
    tm₂.initialState Option.none N₁ tm₁.main tm₁.initialState
    (Turing.initList tm₁ s).stk hlive₁
  have hP1' : (fun c : Option (ShiTM2.CompCfg tm₁ tm₂) =>
        c.bind (Turing.TM2.step (ShiTM2.compM tm₁ tm₂ tr dflt)))^[N₁]
        (Option.some (ShiTM2.liftCfg₁ tm₁ tm₂ T₀ tm₂.initialState Option.none
          (⟨Option.some tm₁.main, tm₁.initialState, (Turing.initList tm₁ s).stk⟩ :
            Turing.TM2.Cfg tm₁.Γ tm₁.Λ tm₁.σ)))
      = Option.some (ShiTM2.liftCfg₁ tm₁ tm₂ T₀ tm₂.initialState Option.none
          (Turing.haltList tm₁ t)) := by
    first
      | (rw [hP1, e₁']
         done)
      | (rw [hP1, e₁']
         rfl
         done)
      | (rw [hP1, e₁']
         simp
         done)
  -- **The halt redirection.**  `Turing.haltList tm₁ t` has label `none`, which `liftCfg₁` sends
  -- to the live label `lcopyA`; the internal state is `compInitialState` on the nose.
  have hB : ShiTM2.liftCfg₁ tm₁ tm₂ T₀ tm₂.initialState Option.none (Turing.haltList tm₁ t)
      = (⟨Option.some (ShiTM2.lcopyA tm₁ tm₂), ShiTM2.compInitialState tm₁ tm₂,
          (ShiTM2.liftCfg₁ tm₁ tm₂ T₀ tm₂.initialState Option.none
            (Turing.haltList tm₁ t)).stk⟩ : ShiTM2.CompCfg tm₁ tm₂) := by
    refine shiAsm_cfg_ext ?_ ?_ (fun _ => rfl)
    · have hl : (ShiTM2.liftCfg₁ tm₁ tm₂ T₀ tm₂.initialState Option.none
          (Turing.haltList tm₁ t)).l
          = Option.some ((Turing.haltList tm₁ t).l.elim (ShiTM2.lcopyA tm₁ tm₂)
              (ShiTM2.injΛ₁ tm₁ tm₂)) := rfl
      first
        | (rw [hl, hh1l]
           done)
        | (rw [hl, hh1l]
           rfl
           done)
        | (rw [hl, hh1l]
           simp
           done)
    · have hv : (ShiTM2.liftCfg₁ tm₁ tm₂ T₀ tm₂.initialState Option.none
          (Turing.haltList tm₁ t)).var
          = (((Turing.haltList tm₁ t).var, tm₂.initialState, Option.none) :
              ShiTM2.Compσ tm₁ tm₂) := rfl
      first
        | (rw [hv, hh1v]
           done)
        | (rw [hv, hh1v]
           rfl
           done)
        | (rw [hv, hh1v]
           simp
           done)
  -- Make the handover stack family an OPAQUE LOCAL, packaging now -- while the concrete form is
  -- still in scope and `exact` can check it at default transparency -- everything phase 2 and the
  -- phase-3 matching will need from it.  Nothing downstream ever traverses a hypothesis whose
  -- type mentions a `CompΓ`-indexed dependent function or `List.map`.
  obtain ⟨Sm, hSmcfg, hSmk₁, hSmscr, hSmoth, hSminj⟩ :
      ∃ Sm : ∀ k, List (ShiTM2.CompΓ tm₁ tm₂ k),
        ShiTM2.liftCfg₁ tm₁ tm₂ T₀ tm₂.initialState Option.none (Turing.haltList tm₁ t)
          = (⟨Option.some (ShiTM2.lcopyA tm₁ tm₂), ShiTM2.compInitialState tm₁ tm₂, Sm⟩ :
              ShiTM2.CompCfg tm₁ tm₂)
        ∧ Sm (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁) = t
        ∧ Sm (ShiTM2.kScr tm₁ tm₂) = []
        ∧ (∀ i : tm₁.K, i ≠ tm₁.k₁ → Sm (ShiTM2.injK₁ tm₁ tm₂ i) = [])
        ∧ (∀ j : tm₂.K, Sm (ShiTM2.injK₂ tm₁ tm₂ j) = []) :=
    ⟨_, hB, hh1k₁, hT₀ (ShiTM2.kScr tm₁ tm₂), fun i hi => hh1ne i hi,
      fun j => hT₀ (ShiTM2.injK₂ tm₁ tm₂ j)⟩
  -- **Phase 2.**  The register conjunct `hv'` is what pins all three coordinates of the state.
  obtain ⟨v', S', hIter, -, hS'k₀, hS'k₁, hS'scr, hS'oth, hv'⟩ :=
    ShiTM.copy_phase_transfers_output_state tm₁ tm₂ tr dflt
      (ShiTM2.compInitialState tm₁ tm₂) Sm hSmscr (hSminj tm₂.k₀)
  have hlen : (Sm (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)).length = t.length :=
    congrArg List.length hSmk₁
  have hP2 : (fun c : Option (ShiTM2.CompCfg tm₁ tm₂) =>
        c.bind (Turing.TM2.step (ShiTM2.compM tm₁ tm₂ tr dflt)))^[2 * t.length + 2]
        (Option.some (⟨Option.some (ShiTM2.lcopyA tm₁ tm₂),
          ShiTM2.compInitialState tm₁ tm₂, Sm⟩ : ShiTM2.CompCfg tm₁ tm₂))
      = Option.some (⟨Option.some (ShiTM2.injΛ₂ tm₁ tm₂ tm₂.main), v', S'⟩ :
          ShiTM2.CompCfg tm₁ tm₂) := by
    first
      | (rw [← hlen]
         exact hIter
         done)
      | (have hI := hIter
         rw [hlen] at hI
         exact hI
         done)
  -- **Phase 2 to phase 3.**  The post-transfer configuration is the `liftCfg₂`-lift of
  -- `Turing.initList tm₂ (t.map tr)`.  `l` and `var` are `rfl` and `hv'`; the stacks need the
  -- per-key clauses of the transfer plus the laws at `tm₁` and `tm₂`.
  have hC : (⟨Option.some (ShiTM2.injΛ₂ tm₁ tm₂ tm₂.main), v', S'⟩ : ShiTM2.CompCfg tm₁ tm₂)
      = ShiTM2.liftCfg₂ tm₁ tm₂ T₀ tm₁.initialState Option.none
          (⟨Option.some tm₂.main, tm₂.initialState,
            (Turing.initList tm₂ (t.map tr)).stk⟩ : Turing.TM2.Cfg tm₂.Γ tm₂.Λ tm₂.σ) := by
    refine shiAsm_cfg_ext rfl hv' ?_
    intro k
    rcases k with i | j | w
    · by_cases hi : i = tm₁.k₁
      · subst hi
        exact hS'k₁.trans (hT₀ (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)).symm
      · exact (hS'oth (ShiTM2.injK₁ tm₁ tm₂ i) (shiAsm_ne_inl hi)
            (shiAsm_ne_inl_inr i (Sum.inl tm₂.k₀))
            (shiAsm_ne_inl_inr i (Sum.inr ()))).trans
          ((hSmoth i hi).trans (hT₀ (ShiTM2.injK₁ tm₁ tm₂ i)).symm)
    · by_cases hj : j = tm₂.k₀
      · subst hj
        exact hS'k₀.trans
          ((congrArg
              (fun L : List (ShiTM2.CompΓ tm₁ tm₂ (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)) =>
                List.map (tr : ShiTM2.CompΓ tm₁ tm₂ (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁) →
                  ShiTM2.CompΓ tm₁ tm₂ (ShiTM2.injK₂ tm₁ tm₂ tm₂.k₀)) L)
              hSmk₁).trans hi2k₀.symm)
      · exact (hS'oth (ShiTM2.injK₂ tm₁ tm₂ j) (shiAsm_ne_inr_inl tm₁.k₁ (Sum.inl j))
            (shiAsm_ne_inr (shiAsm_ne_inl hj))
            (shiAsm_ne_inr (shiAsm_ne_inl_inr j ()))).trans
          ((hSminj j).trans (hi2ne j hj).symm)
    · first
        | (exact hS'scr.trans (hT₀ (ShiTM2.kScr tm₁ tm₂)).symm
           done)
        | (cases w
           exact hS'scr.trans (hT₀ (ShiTM2.kScr tm₁ tm₂)).symm
           done)
  -- **Phase 3.**
  obtain ⟨hP3, -⟩ := ShiTM.iterate_compM_two_simulation tm₁ tm₂ tr dflt T₀
    tm₁.initialState Option.none N₂ tm₂.main tm₂.initialState
    (Turing.initList tm₂ (t.map tr)).stk hlive₂
  have hP3' : (fun c : Option (ShiTM2.CompCfg tm₁ tm₂) =>
        c.bind (Turing.TM2.step (ShiTM2.compM tm₁ tm₂ tr dflt)))^[N₂]
        (Option.some (ShiTM2.liftCfg₂ tm₁ tm₂ T₀ tm₁.initialState Option.none
          (⟨Option.some tm₂.main, tm₂.initialState,
            (Turing.initList tm₂ (t.map tr)).stk⟩ : Turing.TM2.Cfg tm₂.Γ tm₂.Λ tm₂.σ)))
      = Option.some (ShiTM2.liftCfg₂ tm₁ tm₂ T₀ tm₁.initialState Option.none
          (Turing.haltList tm₂ u)) := by
    first
      | (rw [hP3, e₂']
         done)
      | (rw [hP3, e₂']
         rfl
         done)
      | (rw [hP3, e₂']
         simp
         done)
  -- **The end is `haltList` of the composite.**  `liftCfg₂` carries the component's halt over as
  -- a halt, so the composite's label is `none`; the state is `compInitialState`, which is what
  -- `Turing.haltList` demands, and the stacks agree key by key.
  have hD : ShiTM2.liftCfg₂ tm₁ tm₂ T₀ tm₁.initialState Option.none (Turing.haltList tm₂ u)
      = Turing.haltList (ShiTM2.comp tm₁ tm₂ tr dflt) u := by
    refine shiAsm_cfg_ext ?_ ?_ ?_
    · have hl : (ShiTM2.liftCfg₂ tm₁ tm₂ T₀ tm₁.initialState Option.none
          (Turing.haltList tm₂ u)).l
          = (Turing.haltList tm₂ u).l.map (ShiTM2.injΛ₂ tm₁ tm₂) := rfl
      first
        | (rw [hl, hh2l, hchl]
           done)
        | (rw [hl, hh2l, hchl]
           rfl
           done)
        | (rw [hl, hh2l, hchl]
           simp
           done)
    · have hv : (ShiTM2.liftCfg₂ tm₁ tm₂ T₀ tm₁.initialState Option.none
          (Turing.haltList tm₂ u)).var
          = ((tm₁.initialState, (Turing.haltList tm₂ u).var, Option.none) :
              ShiTM2.Compσ tm₁ tm₂) := rfl
      first
        | (rw [hv, hh2v, hchv]
           done)
        | (rw [hv, hh2v, hchv]
           rfl
           done)
        | (rw [hv, hh2v, hchv]
           simp
           done)
    · intro k
      rcases k with i | j | w
      · exact (hT₀ (ShiTM2.injK₁ tm₁ tm₂ i)).trans
          (hchne (ShiTM2.injK₁ tm₁ tm₂ i) (shiAsm_ne_inl_inr i (Sum.inl tm₂.k₁))).symm
      · by_cases hj : j = tm₂.k₁
        · subst hj
          exact hh2k₁.trans hchk₁.symm
        · exact (hh2ne j hj).trans
            (hchne (ShiTM2.injK₂ tm₁ tm₂ j) (shiAsm_ne_inr (shiAsm_ne_inl hj))).symm
      · first
          | (exact (hT₀ (ShiTM2.kScr tm₁ tm₂)).trans
               (hchne (ShiTM2.kScr tm₁ tm₂)
                 (shiAsm_ne_inr (shiAsm_ne_inr_inl tm₂.k₁ ()))).symm
             done)
          | (cases w
             exact (hT₀ (ShiTM2.kScr tm₁ tm₂)).trans
               (hchne (ShiTM2.kScr tm₁ tm₂)
                 (shiAsm_ne_inr (shiAsm_ne_inr_inl tm₂.k₁ ()))).symm
             done)
  -- **Assemble.**  `Function.iterate_add_apply` (`Logic/Function/Iterate.lean:76`) splits the
  -- index; `StateTransition.EvalsToInTime.trans` is not used, since only the iterate equations
  -- are needed and its index is reversed.
  have hchain : (fun c : Option (ShiTM2.CompCfg tm₁ tm₂) =>
        c.bind (Turing.TM2.step (ShiTM2.compM tm₁ tm₂ tr dflt)))^[
          N₂ + ((2 * t.length + 2) + N₁)]
        (Option.some (Turing.initList (ShiTM2.comp tm₁ tm₂ tr dflt) s))
      = Option.some (Turing.haltList (ShiTM2.comp tm₁ tm₂ tr dflt) u) := by
    first
      | (rw [Function.iterate_add_apply, Function.iterate_add_apply, hA, hP1', hSmcfg, hP2,
            hC, hP3', hD]
         done)
      | (rw [Function.iterate_add_apply, Function.iterate_add_apply, hA, hP1', hSmcfg, hP2,
            hC, hP3', hD]
         rfl
         done)
  -- Identify the binder instance with the one `(comp ..).step` actually carries.  `subst`
  -- retypes the hypotheses without re-elaborating them, which `rw .. at` would.
  have hinst : inst = Turing.FinTM2.decidableEqK (ShiTM2.comp tm₁ tm₂ tr dflt) :=
    shiAsm_decEq_unique _ _
  first
    | (subst hinst)
    | (rw [hinst] at hchain)
  first
    | (show Nonempty (StateTransition.EvalsToInTime (ShiTM2.comp tm₁ tm₂ tr dflt).step
          (Turing.initList (ShiTM2.comp tm₁ tm₂ tr dflt) s)
          (Option.some (Turing.haltList (ShiTM2.comp tm₁ tm₂ tr dflt) u))
          (m₁ + (2 * t.length + 2) + m₂)))
    | skip
  refine ⟨⟨⟨N₂ + ((2 * t.length + 2) + N₁), ?_⟩, ?_⟩⟩
  · first
      | (exact hchain
         done)
      | (simpa only [flip, Turing.FinTM2.step] using hchain
         done)
      | (simpa only [flip] using hchain
         done)
  · -- `omega` treats `{ steps := …, … }.steps` as an OPAQUE ATOM instead of reducing the
    -- projection, so it could not see that the goal's bound and `hle₁`/`hle₂` speak about the
    -- same numbers (its counterexample listed them as unrelated atoms `b`, `d`, `f`).
    -- Both the bounds and the goal are therefore restated in `N₁`/`N₂`; each step is iota.
    have hb₁ : N₁ ≤ m₁ := hle₁
    have hb₂ : N₂ ≤ m₂ := hle₂
    first
      | (show N₂ + ((2 * t.length + 2) + N₁) ≤ m₁ + (2 * t.length + 2) + m₂
         omega
         done)
      | (dsimp only
         omega
         done)
      | omega
