-- Prove2me | solution 1 for ThreeSumSharpTail.pruned_lop_detection
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T21:27:44.654572+00:00
-- url     : https://prove2.me/submissions/49135b57-ab3c-4e69-bd0b-28456716f7fb

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSP299791_Defs5
import Theorems.Thm_ThreeSumSharpTail_pruned_program_solves
import Theorems.Thm_ThreeSumSharpTail_rational_power_representation
import Theorems.Thm_ThreeSumSharpTail_pruned_offline_steps
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/- These short reusable proof bodies are copied from the accepted full-D host.  The
   flattened definitions intentionally omit library lemmas used by its source. -/
namespace Light

variable {lim : Limits} {P : Program} {d : ℕ} {l : List ℤ} {μ : ℕ → ℤ}
  {T : ℕ} {Q : State → Prop}

theorem getElem?_append_of_eq_some {P : Program} {p : ℕ} {body : Stmt}
    (h : P[p]? = some body) (R : Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h

theorem Ends.seq {σ T s₁ s₂} {Q : State → Prop} (T₁ T₂ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' T₂ Q)
    (hT : T₁ + T₂ ≤ T) : Ends lim P d (.seq s₁ s₂) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .seq he₁ he₂, by omega, hq⟩

theorem Ends.while {σ c s} {Q : State → Prop} (I : ℕ → State → Prop) (n : ℕ) (b : ℕ → ℕ)
    (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ (b i) (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ) :
    Ends lim P d (.while c s) σ (∑ i ∈ Finset.range n, (c.cost + 1 + b i) + (c.cost + 1)) Q := by
  have aux : ∀ j i σ, i + j = n → I i σ →
      Ends lim P d (.while c s) σ
        (∑ k ∈ Finset.range j, (c.cost + 1 + b (i + k)) + (c.cost + 1)) Q := by
    intro j
    induction j with
    | zero =>
      intro i σ hij hi
      have hEq : i = n := by omega
      subst i
      obtain ⟨h1, h2, h3⟩ := hn σ hi
      exact ⟨σ, _, .whileFalse h1 h2, by simp, h3⟩
    | succ j ih =>
      intro i σ hij hi
      obtain ⟨h1, h2, σ', k₁, he₁, hk₁, hi'⟩ := hs i σ (by omega) hi
      obtain ⟨σ'', k₂, he₂, hk₂, hq⟩ := ih (i + 1) σ' (by omega) hi'
      refine ⟨σ'', _, .whileTrue h1 h2 he₁ he₂, ?_, hq⟩
      rw [Finset.sum_range_succ']
      have hshift : ∀ k, i + 1 + k = i + (k + 1) := by intro k; omega
      simp only [hshift] at hk₂
      simp only [Nat.add_zero]
      omega
  simpa using aux n 0 σ (by omega) hI

theorem Ends.whileConst {σ c s T} {Q : State → Prop} (I : ℕ → State → Prop) (n b : ℕ)
    (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ b (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + b) + (c.cost + 1) ≤ T) : Ends lim P d (.while c s) σ T Q := by
  obtain ⟨σ', c', he, hc, hq⟩ := Ends.while I n (fun _ => b) hI hs hn
  exact ⟨σ', c', he, by
    have hsum : (∑ i ∈ Finset.range n, (c.cost + 1 + b) + (c.cost + 1)) =
        n * (c.cost + 1 + b) + (c.cost + 1) := by simp [Finset.sum_const, Nat.mul_comm]
    rw [hsum] at hc
    exact hc.trans hT, hq⟩

theorem frame_setLocal : ∀ (l : List ℤ) (x : ℕ) (z : ℤ) (y : ℕ),
    frame (setLocal l x z) y = if y = x then z else frame l y
  | [], 0, z, 0 => by simp
  | [], 0, z, y + 1 => by simp
  | [], x + 1, z, 0 => by simp
  | [], x + 1, z, y + 1 => by simpa using frame_setLocal [] x z y
  | a :: l, 0, z, 0 => by simp
  | a :: l, 0, z, y + 1 => by simp
  | a :: l, x + 1, z, 0 => by simp
  | a :: l, x + 1, z, y + 1 => by simpa using frame_setLocal l x z y

theorem update_frame_setLocal (l : List ℤ) (x : ℕ) (z : ℤ) :
    Function.update (frame l) x z = frame (setLocal l x z) := by
  funext y
  rw [frame_setLocal, Function.update_apply]

theorem wrote_zero {μ : ℕ → ℤ} {dst : ℕ} {f : ℕ → ℤ} : wrote μ dst f 0 = μ := by
  funext a
  unfold wrote
  rw [if_neg (by omega)]

theorem wrote_done {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ} {i : ℕ} (h : i < j) :
    wrote μ dst f j (dst + i) = f i := by
  unfold wrote
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

theorem wrote_rest {μ : ℕ → ℤ} {dst j a : ℕ} {f : ℕ → ℤ} (h : Outside dst j a) :
    wrote μ dst f j a = μ a := by
  unfold wrote
  rw [if_neg (by omega)]

theorem wrote_succ {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ} :
    Function.update (wrote μ dst f j) (dst + j) (f j) = wrote μ dst f (j + 1) := by
  funext a
  by_cases h : a = dst + j
  · subst h
    rw [Function.update_self, wrote_done (Nat.lt_succ_self j)]
  · rw [Function.update_of_ne h]
    unfold wrote
    by_cases h' : dst ≤ a ∧ a < dst + j
    · rw [if_pos h', if_pos (by omega)]
    · rw [if_neg h', if_neg (by omega)]

theorem Ends.mono {s σ T T' Q Q'} (h : Ends lim P d s σ T Q) (hT : T ≤ T')
    (hQ : ∀ σ', Q σ' → Q' σ') : Ends lim P d s σ T' Q' := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc.trans hT, hQ _ hq⟩

theorem Ends.set {σ T x e} {Q : State → Prop} (hs : e.Safe lim σ) (hT : e.cost + 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (e.val σ) }) :
    Ends lim P d (.set x e) σ T Q := ⟨_, _, .set hs, hT, h⟩

theorem Ends.call {σ T p args x body} {Q : State → Prop} (T' : ℕ)
    (ha : ∀ e ∈ args, e.Safe lim σ) (hp : P[p]? = some body) (hd : d < lim.depth)
    (h : Ends lim P (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ T'
      fun σ' => Q ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) :
    Ends lim P d (.call p args x) σ T Q := by
  obtain ⟨σ', k, he, hk, hq⟩ := h
  exact ⟨_, _, .call ha hp hd he, by omega, hq⟩

theorem Ends.iteLast {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d s₁ σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by
      have := Light.Std.space_le (by assumption)
      have := Light.Std.const_le (by assumption)
      simp [Light.Limits.Addr, abs_le, -abs_mul] <;> omega)
    (hT : c.cost + 1 ≤ T := by simp [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost] <;> omega) :
    Ends lim P d (.ite c s₁ s₂) σ T Q := by
  by_cases hv : c.Holds σ
  · obtain ⟨σ', k, he, hk, hq⟩ := h₁ hv
    exact ⟨σ', _, .iteTrue hs hv he, by omega, hq⟩
  · obtain ⟨σ', k, he, hk, hq⟩ := h₂ hv
    exact ⟨σ', _, .iteFalse hs hv he, by omega, hq⟩

theorem Ends.ite {σ T c s₁ s₂} {Q : State → Prop} (T' : ℕ) (hs : c.Safe lim σ)
    (h₁ : c.Holds σ → Ends lim P d s₁ σ T' Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ T' Q)
    (hT : c.cost + 1 + T' ≤ T) : Ends lim P d (.ite c s₁ s₂) σ T Q := by
  by_cases hv : c.Holds σ
  · obtain ⟨σ', k, he, hk, hq⟩ := h₁ hv
    exact ⟨σ', _, .iteTrue hs hv he, by omega, hq⟩
  · obtain ⟨σ', k, he, hk, hq⟩ := h₂ hv
    exact ⟨σ', _, .iteFalse hs hv he, by omega, hq⟩

theorem Ends.skip {σ T} {Q : State → Prop} (h : Q σ) : Ends lim P d .skip σ T Q :=
  ⟨σ, 0, .skip, Nat.zero_le _, h⟩

theorem Ends.store {σ T a e} {Q : State → Prop} (ha : a.Safe lim σ) (he : e.Safe lim σ)
    (hA : lim.Addr (a.val σ)) (hT : a.cost + e.cost + 1 ≤ T)
    (h : Q { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }) :
    Ends lim P d (.store a e) σ T Q := ⟨_, _, .store ha he hA, hT, h⟩

theorem Ends.storeTo {a e : Expr} (b : ℕ) (z : ℤ)
    (h : Q ⟨frame l, Function.update μ b z⟩)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space := by
      have := Light.Std.space_le (by assumption)
      have := Light.Std.const_le (by assumption)
      simp [Light.Limits.Addr, abs_le, -abs_mul] <;> omega)
    (hT : a.cost + e.cost + 1 ≤ T := by simp [Light.Stmt.blockCost, Light.Expr.cost] <;> omega) :
    Ends lim P d (.store a e) ⟨frame l, μ⟩ T Q := by
  obtain ⟨⟨ha, hav⟩, ⟨he', hev⟩, hb⟩ := he
  refine Ends.store ha he' ?_ hT ?_
  · rw [hav]
    exact ⟨Int.natCast_nonneg b, by exact_mod_cast hb⟩
  · rw [hav, hev, Int.toNat_natCast]
    exact h

theorem Ends.for {σ : State} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n b : ℕ)
    (start : I 0 { σ with loc := Function.update σ.loc i 0 })
    (round : ∀ (j : ℕ) (σ : State), j < n → σ.loc i = j → I j σ →
      Ends lim P d body σ b fun σ' =>
        σ'.loc i = j ∧ I (j + 1) { σ' with loc := Function.update σ'.loc i ((j : ℤ) + 1) })
    (done : ∀ σ : State, σ.loc i = n → I n σ → Q σ)
    (bound : ∀ (j : ℕ) (σ : State), j ≤ n → σ.loc i = j → I j σ →
      hi.Safe lim σ ∧ hi.val σ = n)
    (hn : (n : ℤ) ≤ lim.word)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T) :
    Ends lim P d (Stmt.for i hi body) σ T Q := by
  have h0 : (0 : ℤ) ≤ lim.word := le_trans (Int.natCast_nonneg n) hn
  refine Ends.seq 2 (n * (hi.cost + b + 7) + hi.cost + 3)
    (Ends.set (by simpa using h0) (by simp) ?_) (by omega)
  refine Ends.whileConst (fun j σ => σ.loc i = j ∧ I j σ) n (b + 4)
    ⟨by simp, by simpa using start⟩ ?_ ?_ (le_of_eq (by simp only [Cond.cost, Expr.cost]; ring))
  · rintro j σ hj ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound j σ hj.le hc hI
    refine ⟨⟨trivial, hs⟩, ?_, Ends.seq b 4 ((round j σ hj hc hI).mono le_rfl ?_) le_rfl⟩
    · change σ.loc i < hi.val σ
      rw [hc, hv]
      exact_mod_cast hj
    · rintro σ' ⟨hc', hI'⟩
      have hval : (((Light.Expr.op Light.Op.add) (v i) (k 1))).val σ' = (j : ℤ) + 1 := by simp [hc']
      have hj' : (j : ℤ) + 1 ≤ n := by exact_mod_cast hj
      refine Ends.set ⟨trivial, ?_, ?_⟩ (by simp) ⟨?_, ?_⟩
      · change ((1 : ℕ) : ℤ) ≤ lim.word
        push_cast
        omega
      · change |(((Light.Expr.op Light.Op.add) (v i) (k 1))).val σ'| ≤ lim.word
        rw [hval, abs_of_nonneg (by omega)]
        omega
      · simp [hc']
      · rw [hval]
        exact hI'
  · rintro σ ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound n σ le_rfl hc hI
    refine ⟨⟨trivial, hs⟩, ?_, done σ hc hI⟩
    change ¬ σ.loc i < hi.val σ
    rw [hc, hv]
    exact lt_irrefl _

theorem Ends.forMem {loc : ℕ → ℤ} {μ : ℕ → ℤ} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ}
    {Q : State → Prop} (I : ℕ → (ℕ → ℤ) → Prop) (n b : ℕ) (start : I 0 μ)
    (round : ∀ (j : ℕ) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body ⟨Function.update loc i j, μ'⟩ b fun σ' =>
        σ'.loc = Function.update loc i j ∧ I (j + 1) σ'.mem)
    (done : ∀ μ' : ℕ → ℤ, I n μ' → Q ⟨Function.update loc i n, μ'⟩)
    (bound : ∀ (j : ℕ) (μ' : ℕ → ℤ), j ≤ n → I j μ' →
      hi.Safe lim ⟨Function.update loc i j, μ'⟩ ∧ hi.val ⟨Function.update loc i j, μ'⟩ = n)
    (hn : (n : ℤ) ≤ lim.word)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T) :
    Ends lim P d (Stmt.for i hi body) ⟨loc, μ⟩ T Q := by
  refine Ends.for (fun j σ => σ.loc = Function.update loc i j ∧ I j σ.mem) n b
    ⟨by simp, start⟩ ?_ ?_ ?_ hn hT
  · rintro j ⟨_, μ'⟩ hj - ⟨rfl, hI⟩
    refine (round j μ' hj hI).mono le_rfl ?_
    rintro ⟨_, μ''⟩ ⟨rfl, hI'⟩
    exact ⟨by simp, by simp, hI'⟩
  · rintro ⟨_, μ'⟩ - ⟨rfl, hI⟩
    exact done μ' hI
  · rintro j ⟨_, μ'⟩ hj - ⟨rfl, hI⟩
    exact bound j μ' hj hI

theorem Ends.next {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop} (T₁ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' (T - T₁) Q)
    (hT : T₁ ≤ T) : Ends lim P d (Light.Stmt.seq s₁ s₂) σ T Q :=
  Ends.seq T₁ (T - T₁) h (by omega)

theorem Ends.forFrame {i : ℕ} {hi : Expr} {body : Stmt} (I : ℕ → (ℕ → ℤ) → Prop) (n : ℕ)
    (start : I 0 μ)
    (round : ∀ (j : ℕ) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body ⟨frame (setLocal l i j), μ'⟩ body.blockCost fun σ' =>
        σ'.loc = frame (setLocal l i j) ∧ I (j + 1) σ'.mem)
    (done : ∀ μ' : ℕ → ℤ, I n μ' → Q ⟨frame (setLocal l i n), μ'⟩)
    (bound : ∀ (j : ℕ) (μ' : ℕ → ℤ), j ≤ n → I j μ' →
      hi.Gives lim ⟨frame (setLocal l i j), μ'⟩ n := by intros; (((try have := Light.Std.space_le (by assumption)));
                                                                       ((try have := Light.Std.const_le (by assumption)));
                                                                       (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + body.blockCost + 7) + hi.cost + 5 ≤ T := by first
                                                                       |
                                                                         ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                               List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                           (first
                                                                             | omega
                                                                             | ((ring_nf); (omega))))
                                                                       | omega
                                                                       |
                                                                         (simp [] <;>
                                                                             first
                                                                             | omega
                                                                             | ((ring_nf); (omega)))) :
    Ends lim P d (Stmt.for i hi body) ⟨frame l, μ⟩ T Q := by
  refine Ends.forMem I n body.blockCost start ?_ ?_ ?_ hn hT
  · intro j μ' hj hI
    rw [update_frame_setLocal]
    exact round j μ' hj hI
  · intro μ' hI
    rw [update_frame_setLocal]
    exact done μ' hI
  · intro j μ' hj hI
    rw [update_frame_setLocal]
    exact bound j μ' hj hI


































/-! ## Locals by name, and locals whose values do not matter -/




































































section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}

























/-! ## A piece of program text with a lemma of its own -/

variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}































/-! ## Counting loops with scratch variables -/













































end


theorem SolvesN.meets {task : TaskN} {P₀ : Program} {p : ℕ} {T₀ : List ℕ → ℕ}
    {need : List ℕ → Need} (h : SolvesN task P₀ p T₀ need) (R : Program) {lim : Limits} {d : ℕ}
    (x : task.Inst) {μ : ℕ → ℤ} {fr : ℕ} (hpre : task.Pre x μ fr)
    (hok : (need (task.pars x)).Ok lim fr d) :
    Meets lim (P₀ ++ R) p d (task.args x ++ [(fr : ℤ)]) μ (T₀ (task.pars x))
      (task.Post x μ fr) := by
  obtain ⟨body, hp, hb⟩ := h
  exact ⟨body, getElem?_append_of_eq_some hp R, hb R lim d x μ fr hpre hok⟩

theorem Ends.callLast {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ}
    {args : List Expr} {vals : List ℤ} {R : ℤ → (ℕ → ℤ) → Prop} {Q : State → Prop}
    (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨Function.update loc x r, μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨loc, μ⟩) ∧ args.map (·.val ⟨loc, μ⟩) = vals)
    (hd : d < lim.depth)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) :
    Ends lim P d (.call p args x) ⟨loc, μ⟩ T Q := by
  obtain ⟨body, hb, he⟩ := hp
  obtain ⟨hs, rfl⟩ := ha
  exact Ends.call T' hs hb hd (he.mono le_rfl fun _ hR => h _ _ hR) hT

theorem Ends.callTo {p : ℕ} {args : List Expr} {x : ℕ} {vals : List ℤ} {T' : ℕ}
    {R : ℤ → (ℕ → ℤ) → Prop}
    (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨frame (setLocal l x r), μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals)
    (hd : d < lim.depth) (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) :
    Ends lim P d (.call p args x) ⟨frame l, μ⟩ T Q :=
    Ends.callLast (loc:=frame l) (l:=l) hp
      (fun r μ' hR => update_frame_setLocal l x r ▸ h r μ' hR) ha hd hT

theorem Ends.callToThen {p : ℕ} {args : List Expr} {x : ℕ} {s : Stmt}
    {vals : List ℤ} {T' : ℕ} {R : ℤ → (ℕ → ℤ) → Prop}
    (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Ends lim P d s ⟨frame (setLocal l x r), μ'⟩
      (T - ((args.map Expr.cost).sum + 2 + T')) Q)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals)
    (hd : d < lim.depth)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) :
    Ends lim P d ((Light.Stmt.seq (.call p args x) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.callTo hp h ha hd le_rfl) hT

theorem Need.Ok.mono {r r' : Need} {lim : Limits} {fr fr' d d' : ℕ} (h : r.Ok lim fr d)
    (hw : r'.word ≤ r.word) (hc : fr' + r'.cells ≤ fr + r.cells)
    (hd : d' + r'.depth ≤ d + r.depth) : r'.Ok lim fr' d' :=
  ⟨le_trans (by exact_mod_cast hw) h.word, hc.trans h.cells, h.space, hd.trans h.depth⟩

theorem one_le_polyBound (s k : ℕ) (params : List ℕ) : 1 ≤ polyBound s k params := by
  have : 0 < (params.map (· + 1)).prod := List.prod_pos (by simp)
  exact Nat.mul_pos (by positivity) (by positivity)

theorem polyBound_mul (s s' k : ℕ) (params : List ℕ) :
    2 ^ s' * polyBound s k params = polyBound (s' + s) k params := by
  simp only [polyBound, pow_add, mul_assoc]

theorem polyBound_le_succ (s k : ℕ) (ps : List ℕ) :
    polyBound s k ps + 1 ≤ polyBound (1 + s) k ps := by
  have h1 := one_le_polyBound s k ps
  rw [← polyBound_mul]
  omega

end Light

open Filter Asymptotics

namespace ThreeSumSharpTailRationalRegimeTest

open Light

/-- A straight-line expression for a natural power, using only multiplication. -/
def powExpr (x k : ℕ) : Expr :=
  match k with
  | 0 => .const 1
  | k + 1 => .op .mul (.var x) (powExpr x k)

theorem powExpr_val (σ : State) (x k : ℕ) :
    (powExpr x k).val σ = σ.loc x ^ k := by
  induction k with
  | zero => simp [powExpr, Expr.val]
  | succ k ih => simp [powExpr, Expr.val, Op.eval, ih, pow_succ, mul_comm]

theorem pow_le_pow_of_one_le {n : ℕ} (hn : 1 ≤ n) {i j : ℕ} (hij : i ≤ j) :
    n ^ i ≤ n ^ j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [pow_add]
  have hk : 1 ≤ n ^ k := Nat.one_le_pow _ _ hn
  calc
    n ^ i = n ^ i * 1 := by simp
    _ ≤ n ^ i * n ^ k := Nat.mul_le_mul_left _ hk

theorem powExpr_safe (lim : Limits) (σ : State) (x base exponent : ℕ)
    (hbase : 1 ≤ base) (hloc : σ.loc x = (base : ℤ))
    (hword : (base ^ exponent : ℕ) ≤ lim.word) :
    (powExpr x exponent).Safe lim σ := by
  induction exponent with
  | zero => simpa [powExpr, Expr.Safe] using hword
  | succ k ih =>
      simp only [powExpr, Expr.Safe, Expr.val, Op.eval]
      constructor
      · trivial
      constructor
      · apply ih
        have hmono : base ^ k ≤ base ^ (k + 1) :=
          pow_le_pow_of_one_le hbase (by omega)
        have hcast : (base ^ k : ℤ) ≤ (base ^ (k + 1) : ℤ) := by exact_mod_cast hmono
        exact hcast.trans hword
      · have hv : (powExpr x k).val σ * σ.loc x = (base ^ (k + 1) : ℕ) := by
          rw [powExpr_val, hloc]
          norm_cast
        rw [mul_comm (σ.loc x) ((powExpr x k).val σ), hv,
          abs_of_nonneg (Int.natCast_nonneg _)]
        exact_mod_cast hword

def program (A B : ℕ) : Stmt :=
  .seq (.set 2 (powExpr 0 A))
    (.seq (.set 3 (powExpr 1 B))
      (.ite (.lt (.var 2) (.var 3)) (.set 0 (.const 0)) (.set 0 (.const 1))))

def stepCount (A B : ℕ) : ℕ :=
  ((powExpr 0 A).cost + 1) + ((powExpr 1 B).cost + 1 + 6)

theorem rationalRegimeTest_solver (A B : ℕ) :
    ∃ (S : Stmt) (c : ℕ),
      ∀ (lim : Limits) (P : Program) (d : ℕ) (N D : ℕ) (μ : ℕ → ℤ),
        1 ≤ N → 1 ≤ D →
        ((N ^ A + D ^ B + 100 : ℕ) : ℤ) ≤ lim.word →
        Ends lim P d S ⟨frame [N, D], μ⟩ c
          (fun σ => σ.mem = μ ∧
            ((σ.loc 0 = 1 ∧ D ^ B ≤ N ^ A) ∨ (σ.loc 0 = 0 ∧ N ^ A < D ^ B))) := by
  refine ⟨program A B, stepCount A B, ?_⟩
  intro lim P d N D μ hN hD hword
  let σ₀ : State := ⟨frame [N, D], μ⟩
  let σ₁ : State := { σ₀ with loc := Function.update σ₀.loc 2 ((powExpr 0 A).val σ₀) }
  let σ₂ : State := { σ₁ with loc := Function.update σ₁.loc 3 ((powExpr 1 B).val σ₁) }
  let cnd : Cond := .lt (.var 2) (.var 3)
  have hwordA : (N ^ A : ℕ) ≤ lim.word := by
    have hlt : N ^ A ≤ N ^ A + D ^ B + 100 := by omega
    exact (show (N ^ A : ℤ) ≤ (N ^ A + D ^ B + 100 : ℕ) by exact_mod_cast hlt).trans hword
  have hwordB : (D ^ B : ℕ) ≤ lim.word := by
    have hlt : D ^ B ≤ N ^ A + D ^ B + 100 := by omega
    exact (show (D ^ B : ℤ) ≤ (N ^ A + D ^ B + 100 : ℕ) by exact_mod_cast hlt).trans hword
  have hsafeA : (powExpr 0 A).Safe lim σ₀ := by
    apply powExpr_safe lim σ₀ 0 N A hN
    · simp [σ₀, frame]
    · exact hwordA
  have hsafeB : (powExpr 1 B).Safe lim σ₁ := by
    apply powExpr_safe lim σ₁ 1 D B hD
    · simp [σ₁, σ₀, frame]
    · exact hwordB
  have hvalA : (powExpr 0 A).val σ₀ = (N ^ A : ℕ) := by
    rw [powExpr_val]
    simp [σ₀, frame]
  have hvalB : (powExpr 1 B).val σ₁ = (D ^ B : ℕ) := by
    rw [powExpr_val]
    simp [σ₁, σ₀, frame]
  have hcnd : cnd.Safe lim σ₂ := by
    simp [cnd, Cond.Safe]
  have hcondval : cnd.Holds σ₂ ↔ (N ^ A : ℤ) < D ^ B := by
    change σ₂.loc 2 < σ₂.loc 3 ↔ _
    have hloc2 : σ₂.loc 2 = (N ^ A : ℤ) := by simp [σ₂, σ₁, σ₀, hvalA]
    have hloc3 : σ₂.loc 3 = (D ^ B : ℤ) := by
      change Function.update σ₁.loc 3 ((powExpr 1 B).val σ₁) 3 = _
      simp [hvalB]
    rw [hloc2, hloc3]
  have hseqA : Exec lim P d (.set 2 (powExpr 0 A)) σ₀ σ₁ ((powExpr 0 A).cost + 1) := by
    simpa [σ₁, σ₀] using (Exec.set hsafeA : Exec lim P d (.set 2 (powExpr 0 A)) σ₀
      { σ₀ with loc := Function.update σ₀.loc 2 ((powExpr 0 A).val σ₀) } ((powExpr 0 A).cost + 1))
  have hseqB : Exec lim P d (.set 3 (powExpr 1 B)) σ₁ σ₂ ((powExpr 1 B).cost + 1) := by
    simpa [σ₂] using (Exec.set hsafeB : Exec lim P d (.set 3 (powExpr 1 B)) σ₁
      { σ₁ with loc := Function.update σ₁.loc 3 ((powExpr 1 B).val σ₁) } ((powExpr 1 B).cost + 1))
  have hword100 : (100 : ℤ) ≤ lim.word := by
    have : (100 : ℤ) ≤ (N ^ A + D ^ B + 100 : ℕ) := by exact_mod_cast (by omega : 100 ≤ N ^ A + D ^ B + 100)
    exact this.trans hword
  by_cases hlt : (N ^ A : ℤ) < D ^ B
  · have hbranch : Exec lim P d (.set 0 (.const 0)) σ₂
        { σ₂ with loc := Function.update σ₂.loc 0 0 } 2 := by
      exact Exec.set (by simp [Expr.Safe]; omega)
    have hite : Exec lim P d (.ite cnd (.set 0 (.const 0)) (.set 0 (.const 1))) σ₂
        { σ₂ with loc := Function.update σ₂.loc 0 0 }
        (cnd.cost + 1 + 2) :=
      Exec.iteTrue hcnd (hcondval.mpr hlt) hbranch
    have hexec : Exec lim P d (program A B) σ₀
        { σ₂ with loc := Function.update σ₂.loc 0 0 } (stepCount A B) := by
      simpa [program, stepCount, cnd, Cond.cost] using Exec.seq hseqA (Exec.seq hseqB hite)
    refine ⟨_, stepCount A B, hexec, le_rfl, ?_⟩
    constructor
    · simp [σ₂, σ₁, σ₀, Function.update]
    · right
      constructor
      · simp [σ₂, σ₁, σ₀, Function.update, hvalA, hvalB]
      · exact_mod_cast hlt
  · have hbranch : Exec lim P d (.set 0 (.const 1)) σ₂
        { σ₂ with loc := Function.update σ₂.loc 0 1 } 2 := by
      exact Exec.set (by simp [Expr.Safe]; omega)
    have hite : Exec lim P d (.ite cnd (.set 0 (.const 0)) (.set 0 (.const 1))) σ₂
        { σ₂ with loc := Function.update σ₂.loc 0 1 }
        (cnd.cost + 1 + 2) :=
      Exec.iteFalse hcnd (fun hh => hlt (hcondval.mp hh)) hbranch
    have hexec : Exec lim P d (program A B) σ₀
        { σ₂ with loc := Function.update σ₂.loc 0 1 } (stepCount A B) := by
      simpa [program, stepCount, cnd, Cond.cost] using Exec.seq hseqA (Exec.seq hseqB hite)
    refine ⟨_, stepCount A B, hexec, le_rfl, ?_⟩
    constructor
    · simp [σ₂, σ₁, σ₀, Function.update]
    · left
      constructor
      · simp [σ₂, σ₁, σ₀, Function.update, hvalA, hvalB]
      · have hnlt : ¬ ((N ^ A : ℤ) < D ^ B) := hlt
        exact_mod_cast (not_lt.mp hnlt)

end ThreeSumSharpTailRationalRegimeTest

namespace Light.Sec2

def thinFrameArgs (x : ThinInst) : List Expr :=
  [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9]

def thinFrameArgs01 : List Expr := [v 0, v 1]

def thinFrameLocs (x : ThinInst) (fr : ℕ) : List ℤ :=
  [(x.N : ℤ), (x.D : ℤ), (x.w : ℤ), (x.U : ℤ), (x.x : ℤ), (x.y : ℤ),
    (x.wi : ℤ), (x.wj : ℤ), (x.out : ℤ), (fr : ℤ)]

def thinFrameState (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ) (r : ℤ) : State :=
  ⟨frame (setLocal (thinFrameLocs x fr) 10 r), μ⟩

theorem thinFrame_args_safe (lim : Limits) (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ) (r : ℤ)
    (_std : Std lim) (_hpre : x.Pre μ fr) (_hfr : fr ≤ lim.space)
    (_hU : x.U = 1) (_hr : |r| ≤ lim.word) :
    ∀ e ∈ thinFrameArgs x, e.Safe lim (thinFrameState x μ fr r) := by
  intro e _he
  simp only [thinFrameArgs, List.mem_cons, List.mem_singleton] at _he
  rcases _he with h | h | h | h | h | h | h | h | h | h <;>
    simp_all [Expr.Safe, v]

theorem thinFrame_args_vals (lim : Limits) (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ) (r : ℤ)
    (_std : Std lim) (_hpre : x.Pre μ fr) (_hfr : fr ≤ lim.space)
    (_hU : x.U = 1) (_hr : |r| ≤ lim.word) :
    (thinFrameArgs x).map (fun e => e.val (thinFrameState x μ fr r)) =
      [(x.N : ℤ), (x.D : ℤ), (x.w : ℤ), (x.U : ℤ), (x.x : ℤ), (x.y : ℤ),
        (x.wi : ℤ), (x.wj : ℤ), (x.out : ℤ), (fr : ℤ)] := by
  simp [thinFrameArgs, thinFrameState, thinFrameLocs, Expr.val, Light.frame_setLocal, Light.frame]

theorem thinFrame_args01_safe (lim : Limits) (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ) (r : ℤ)
    (_std : Std lim) (_hpre : x.Pre μ fr) (_hfr : fr ≤ lim.space)
    (_hU : x.U = 1) (_hr : |r| ≤ lim.word) :
    ∀ e ∈ thinFrameArgs01, e.Safe lim (thinFrameState x μ fr r) := by
  intro e _he
  simp only [thinFrameArgs01, List.mem_cons, List.mem_singleton] at _he
  rcases _he with h | h <;> simp_all [Expr.Safe, v]

theorem thinFrame_args01_vals (lim : Limits) (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ) (r : ℤ)
    (_std : Std lim) (_hpre : x.Pre μ fr) (_hfr : fr ≤ lim.space)
    (_hU : x.U = 1) (_hr : |r| ≤ lim.word) :
    thinFrameArgs01.map (fun e => e.val (thinFrameState x μ fr r)) = [(x.N : ℤ), (x.D : ℤ)] := by
  simp [thinFrameArgs01, thinFrameState, thinFrameLocs, Expr.val, Light.frame_setLocal, Light.frame]

end Light.Sec2

namespace Nat

theorem mul_add_le_mul {a b c : ℕ} (hab : a < b) (_ : c ≤ c) : a * c + c ≤ b * c := by
  have h := Nat.mul_le_mul_right c (Nat.succ_le_of_lt hab)
  simpa [Nat.succ_mul] using h

end Nat

namespace ThreeSumApsp

theorem AbsLe.abs_getD_le {l : List ℤ} {U : ℤ} (hU : 0 ≤ U) (h : AbsLe l U) (i : ℕ) :
    |l.getD i 0| ≤ U := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · have hlen : l.length ≤ i := Nat.le_of_not_lt hi
    rw [List.getD_eq_default _ _ hlen]
    exact hU

end ThreeSumApsp

namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Seg.of_sameOutside {μ μ' : ℕ → ℤ} {b a n : ℕ} {l : List ℤ}
    (h : Seg μ b l) (hs : SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : Seg μ' b l := by
  intro i hi
  rw [hs _ (by omega)]
  exact h i hi

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Ends.of_blockSafe : ∀ {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop},
    s.BlockSafe lim σ → s.blockCost ≤ T → Q (s.after σ) → Ends lim P d s σ T Q
  | .skip, _, _, _, _, _, h => Ends.skip h
  | .set _ _, _, _, _, hs, hT, h => Ends.set hs hT h
  | .store _ _, _, _, _, hs, hT, h => Ends.store hs.1 hs.2.1 hs.2.2 hT h
  | .seq s t, _, _, _, hs, hT, h =>
    Ends.seq s.blockCost t.blockCost
      (Ends.of_blockSafe hs.1 le_rfl (Ends.of_blockSafe hs.2 le_rfl h)) hT
  | .ite c s t, σ, _, _, hs, hT, h =>
    Ends.ite (max s.blockCost t.blockCost) hs.1
      (fun hc => Ends.of_blockSafe (hs.2.1 hc) (le_max_left _ _)
        (by simpa only [Stmt.after, if_pos hc] using h))
      (fun hc => Ends.of_blockSafe (hs.2.2 hc) (le_max_right _ _)
        (by simpa only [Stmt.after, if_neg hc] using h)) hT
  | .while _ _, _, _, _, hs, _, _ => hs.elim
  | .call _ _ _, _, _, _, hs, _, _ => hs.elim

theorem Ends.block {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}
    (h : s.Runs lim σ Q) (hT : s.blockCost ≤ T) : Ends lim P d s σ T Q :=
  Ends.of_blockSafe h.1 hT h.2

theorem Ends.whileBlock {σ : State} {c : Cond} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n : ℕ) (start : I 0 σ)
    (round : ∀ (j : ℕ) (σ : State), j < n → I j σ →
      c.Safe lim σ ∧ c.Holds σ ∧ body.Runs lim σ (I (j + 1)))
    (done : ∀ σ : State, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + body.blockCost) + (c.cost + 1) ≤ T := by
      simp only [Stmt.blockCost, Cond.cost, Expr.cost, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil]
      first | omega | (ring_nf; omega)) :
    Ends lim P d (.while c body) σ T Q :=
  Ends.whileConst I n body.blockCost start
    (fun j σ hj hI => ⟨(round j σ hj hI).1, (round j σ hj hI).2.1,
      Ends.block (round j σ hj hI).2.2 le_rfl⟩) done hT

theorem Ends.skipLast {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s ;; .skip) σ T Q) : Ends lim P d s σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂ => cases he₂; exact ⟨σ', _, he₁, by omega, hq⟩

theorem Ends.seqAssoc {σ : State} {T : ℕ} {s₁ s₂ s₃ : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s₁ ;; (s₂ ;; s₃)) σ T Q) : Ends lim P d ((s₁ ;; s₂) ;; s₃) σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂₃ =>
    cases he₂₃ with
    | seq he₂ he₃ => exact ⟨σ', _, .seq (.seq he₁ he₂) he₃, by omega, hq⟩

theorem Ends.skipThen {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d s σ T Q) : Ends lim P d (.skip ;; s) σ T Q :=
  Ends.seq 0 T (Ends.skip h) (by omega)

theorem Ends.seqSelf {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s₁ ;; s₂) σ T Q) : Ends lim P d (s₁ ;; s₂) σ T Q := h

theorem Ends.setToThen {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}
    {x : ℕ} {e : Expr} {s : Stmt} (z : ℤ)
    (h : Ends lim P d s ⟨frame (setLocal l x z), μ⟩ (T - (e.cost + 1)) Q)
    (he : e.Gives lim ⟨frame l, μ⟩ z) (hT : e.cost + 1 ≤ T) :
    Ends lim P d (.set x e ;; s) ⟨frame l, μ⟩ T Q := by
  refine Ends.next _ (Ends.set he.1 le_rfl ?_) hT
  rw [he.2]
  simp only [update_frame_setLocal]
  exact h

theorem Ends.storeToThen {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}
    {a e : Expr} {s : Stmt} (b : ℕ) (z : ℤ)
    (h : Ends lim P d s ⟨frame l, Function.update μ b z⟩ (T - (a.cost + e.cost + 1)) Q)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space)
    (hT : a.cost + e.cost + 1 ≤ T) : Ends lim P d (.store a e ;; s) ⟨frame l, μ⟩ T Q := by
  obtain ⟨⟨ha, hav⟩, ⟨he', hev⟩, hb⟩ := he
  refine Ends.next _ (Ends.store ha he' ?_ le_rfl ?_) hT
  · rw [hav]
    exact ⟨Int.natCast_nonneg b, by exact_mod_cast hb⟩
  · rw [hav, hev, Int.toNat_natCast]
    exact h
end Light

namespace Light

theorem SameOutside.refl {μ : ℕ → ℤ} {a n : ℕ} : SameOutside μ μ a n := by
  intro b hb
  rfl

theorem frame_append_zeros (l : List ℤ) (n : ℕ) :
    frame (l ++ List.replicate n 0) = frame l := by
  funext y
  simp only [frame, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split_ifs with h1 h2
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega)]
end Light


namespace Light.Sec2

open ThreeSumApsp

variable {x : ThinInst} {m : ℕ} {μ : ℕ → ℤ} {fr : ℕ}

section positions

variable {i : ℕ}

/-- A number of a wanted position is an index of the list of the rows. -/
theorem _root_.Light.ThinInst.Pre.lt_lenWI (hpre : x.Pre μ fr) (hi : i < x.w) : i < x.WI.length :=
  hi.trans_eq hpre.lenWI.symm

/-- A number of a wanted position is an index of the list of the columns. -/
theorem _root_.Light.ThinInst.Pre.lt_lenWJ (hpre : x.Pre μ fr) (hi : i < x.w) : i < x.WJ.length :=
  hi.trans_eq hpre.lenWJ.symm

/-- A number of a wanted position is an index of the list of the positions. -/
theorem _root_.Light.ThinInst.Pre.lt_lenZip (hpre : x.Pre μ fr) (hi : i < x.w) :
    i < (x.WI.zip x.WJ).length := by
  simp [hpre.lenWI, hpre.lenWJ, hi]

theorem thinI_eq (h : i < x.WI.length) : thinI x i = x.WI[i] := List.getD_eq_getElem _ _ h

theorem thinJ_eq (h : i < x.WJ.length) : thinJ x i = x.WJ[i] := List.getD_eq_getElem _ _ h

/-- The rows of the wanted positions are rows of the matrix. -/
theorem thinI_lt (hpre : x.Pre μ fr) (hi : i < x.w) : thinI x i < x.N := by
  rw [thinI_eq (hpre.lt_lenWI hi)]
  exact hpre.ltWI _ (List.getElem_mem _)

/-- The columns of the wanted positions are columns of the matrix. -/
theorem thinJ_lt (hpre : x.Pre μ fr) (hi : i < x.w) : thinJ x i < x.N := by
  rw [thinJ_eq (hpre.lt_lenWJ hi)]
  exact hpre.ltWJ _ (List.getElem_mem _)

/-- The rows of the wanted positions, in the memory. -/
theorem mem_thinI (hpre : x.Pre μ fr) (hi : i < x.w) : μ (x.wi + i) = (thinI x i : ℕ) := by
  rw [thinI_eq (hpre.lt_lenWI hi), hpre.segWI i (by simpa using hpre.lt_lenWI hi),
    List.getElem_map]

/-- The columns of the wanted positions, in the memory. -/
theorem mem_thinJ (hpre : x.Pre μ fr) (hi : i < x.w) : μ (x.wj + i) = (thinJ x i : ℕ) := by
  rw [thinJ_eq (hpre.lt_lenWJ hi), hpre.segWJ i (by simpa using hpre.lt_lenWJ hi),
    List.getElem_map]

end positions

/-- There is one answer for each wanted position. -/
theorem length_thinOut (hpre : x.Pre μ fr) : (thinOut x.N x.D x.X x.Y x.WI x.WJ).length = x.w := by
  simp [thinOut, hpre.lenWI, hpre.lenWJ]

/-- The answer number i. -/
theorem getD_thinOut (hpre : x.Pre μ fr) {i : ℕ} (hi : i < x.w) :
    (thinOut x.N x.D x.X x.Y x.WI x.WJ).getD i 0
      = thinEntry x.N x.D x.X x.Y (thinI x i) (thinJ x i) := by
  rw [thinI_eq (hpre.lt_lenWI hi), thinJ_eq (hpre.lt_lenWJ hi)]
  unfold thinOut
  rw [List.getD_eq_getElem _ _ (by simpa using hpre.lt_lenZip hi), List.getElem_map,
    List.getElem_zip]

end Light.Sec2

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Brute

end Brute

open ThinArg Brute

/-- One more term. -/
theorem brutePartial_succ (N D : ℕ) (X Y : List ℤ) (I J n : ℕ) :
    brutePartial N D X Y I J (n + 1)
      = brutePartial N D X Y I J n + X.getD (I * D + n) 0 * Y.getD (n * N + J) 0 := by
  simp [brutePartial, List.range_succ]

/-- A term of the inner product is at most U². -/
theorem abs_bruteTerm_le {X Y : List ℤ} {U : ℕ} (hX : AbsLe X U) (hY : AbsLe Y U) (a b : ℕ) :
    |X.getD a 0 * Y.getD b 0| ≤ (U * U : ℕ) := by
  rw [abs_mul]
  push_cast
  exact mul_le_mul (hX.abs_getD_le (by positivity) a) (hY.abs_getD_le (by positivity) b)
    (abs_nonneg _) (by positivity)

/-- The first n terms add up to at most n U². -/
theorem abs_brutePartial_le {N D : ℕ} {X Y : List ℤ} {U : ℕ} (hX : AbsLe X U) (hY : AbsLe Y U)
    (I J n : ℕ) : |brutePartial N D X Y I J n| ≤ n * (U * U : ℕ) := by
  induction n with
  | zero => simp [brutePartial]
  | succ n ih =>
    rw [brutePartial_succ]
    calc |brutePartial N D X Y I J n + X.getD (I * D + n) 0 * Y.getD (n * N + J) 0|
        ≤ |brutePartial N D X Y I J n| + |X.getD (I * D + n) 0 * Y.getD (n * N + J) 0| :=
          abs_add_le _ _
      _ ≤ n * (U * U : ℕ) + (U * U : ℕ) := add_le_add ih (abs_bruteTerm_le hX hY _ _)
      _ = ((n + 1 : ℕ) : ℤ) * (U * U : ℕ) := by push_cast; ring

/-- **The inner product** of row I of X and column J of Y. -/
theorem bruteInner_spec (std : Std lim) (x : ThinInst) {μ : ℕ → ℤ} {fr i I J : ℕ} {u : ℤ}
    (segX : Seg μ x.x x.X) (segY : Seg μ x.y x.Y) (lX : x.X.length = x.N * x.D)
    (lY : x.Y.length = x.D * x.N) (bX : AbsLe x.X x.U) (bY : AbsLe x.Y x.U) (hI : I < x.N)
    (hJ : J < x.N) (roomX : x.x + x.N * x.D < lim.space) (roomY : x.y + x.D * x.N + x.N < lim.space)
    (hword : ((x.D * (x.U * x.U) : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d Light.Sec2.bruteInner ⟨Light.frame (bruteLocs x u fr i 0 (x.x + I * x.D) (x.y + J) 0), μ⟩
      (24 * x.D + 4) fun σ' => σ' = ⟨Light.frame (bruteLocs x u fr i x.D (x.x + I * x.D + x.D)
        (x.y + x.D * x.N + J) (brutePartial x.N x.D x.X x.Y I J x.D)), μ⟩ := by
  have hw := std.space_le
  have h100 := std.const_le
  have hID := Nat.mul_add_le_mul hI (le_refl x.D)
  unfold Light.Sec2.bruteInner
  refine Ends.whileBlock (σ := ⟨Light.frame (bruteLocs x u fr i 0 (x.x + I * x.D) (x.y + J) 0), μ⟩)
    (fun t σ => σ = ⟨Light.frame (bruteLocs x u fr i t (x.x + I * x.D + t)
    (x.y + t * x.N + J) (brutePartial x.N x.D x.X x.Y I J t)), μ⟩) x.D
    (by simp [brutePartial]) ?round ?done
  case round =>
    rintro t _ ht rfl
    have htN := Nat.mul_add_le_mul ht (le_refl x.N)
    have rX : μ (x.x + I * x.D + t) = x.X.getD (I * x.D + t) 0 := by
      rw [Nat.add_assoc]
      exact segX.getD (by omega) 0
    have rY : μ (x.y + t * x.N + J) = x.Y.getD (t * x.N + J) 0 := by
      rw [Nat.add_assoc]
      exact segY.getD (by omega) 0
    have hmono : ∀ n ≤ x.D, ((n : ℤ) * (x.U * x.U : ℕ)) ≤ lim.word := fun n hn =>
      le_trans (by exact_mod_cast Nat.mul_le_mul_right (x.U * x.U) hn) hword
    have hsum := abs_le.mp ((abs_brutePartial_le (N := x.N) (D := x.D) bX bY I J (t + 1)).trans
      (by exact_mod_cast hmono (t + 1) (by omega)))
    have hterm := abs_le.mp ((abs_bruteTerm_le bX bY (I * x.D + t) (t * x.N + J)).trans
      (by simpa using hmono 1 (by omega)))
    have hnext := brutePartial_succ x.N x.D x.X x.Y I J t
    rw [hnext] at hsum
    generalize x.X.getD (I * x.D + t) 0 = a, x.Y.getD (t * x.N + J) 0 = b at *
    generalize hpx : x.x + I * x.D + t = px at *
    generalize hpy : x.y + t * x.N + J = py at *
    have hpx' : (px : ℤ) + 1 = x.x + I * x.D + (t + 1) := by rw [← hpx]; push_cast; ring
    have hpy' : (py : ℤ) + x.N = x.y + (t + 1) * x.N + J := by rw [← hpy]; push_cast; ring
    exact ⟨by simp, by simp [bruteLocs]; omega,
      by (( (try have := Light.Std.space_le (by assumption))
            (try have := Light.Std.const_le (by assumption))
            (simp [Light.Limits.Addr, abs_le, -abs_mul, bruteLocs, rX, rY] <;> omega))),
      by simp [bruteLocs, update_frame_setLocal, rX, rY, hnext, hpx', hpy']⟩
  case done =>
    rintro _ rfl
    exact ⟨by simp, by simp [bruteLocs], rfl⟩

/-- **One wanted position.** -/
theorem bruteRound_spec (std : Std lim) {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ} {u : ℤ}
    (hpre : x.Pre μ fr) (hsp : fr + x.N + 1 ≤ lim.space)
    (hword : ((x.D * (x.U * x.U) : ℕ) : ℤ) ≤ lim.word) {i : ℕ} (hi : i < x.w) {σ : State}
    (h : BruteInv x μ u fr i σ) :
    Ends lim P d bruteRound σ (24 * x.D + 33) (BruteInv x μ u fr (i + 1)) := by
  obtain ⟨t, px, py, s, μ', rfl, hdone, hfr⟩ := h
  have hw := std.space_le
  have h100 := std.const_le
  have hbelow := And.intro hpre.belowX (And.intro hpre.belowY (And.intro hpre.belowWI
    (And.intro hpre.belowWJ hpre.belowOut)))
  have hI := thinI_lt hpre hi
  have hJ := thinJ_lt hpre hi
  have segX : Seg μ' x.x x.X :=
    hpre.segX.of_sameOutside hfr (by rw [hpre.lenX]; exact hpre.apartX.symm)
  have segY : Seg μ' x.y x.Y :=
    hpre.segY.of_sameOutside hfr (by rw [hpre.lenY]; exact hpre.apartY.symm)
  have rI : μ' (x.wi + i) = (thinI x i : ℕ) := by
    rw [hfr _ (by rcases hpre.apartWI with h | h <;> omega)]
    exact mem_thinI hpre hi
  have rJ : μ' (x.wj + i) = (thinJ x i : ℕ) := by
    rw [hfr _ (by rcases hpre.apartWJ with h | h <;> omega)]
    exact mem_thinJ hpre hi
  have hidxI : ((x.wi : ℤ) + (i : ℤ)).toNat = x.wi + i := by
    push_cast
    omega
  have hidxJ : ((x.wj : ℤ) + (i : ℤ)).toNat = x.wj + i := by
    push_cast
    omega
  have rIcast : μ' (((x.wi : ℤ) + (i : ℤ)).toNat) = (thinI x i : ℤ) := by
    rw [hidxI, rI]
  have rJcast : μ' (((x.wj : ℤ) + (i : ℤ)).toNat) = (thinJ x i : ℤ) := by
    rw [hidxJ, rJ]
  have hID := Nat.mul_add_le_mul hI (le_refl x.D)
  have hND : x.N ≤ x.D * x.N := Nat.le_mul_of_pos_left _ hpre.D_pos
  unfold bruteRound bruteLocs
  -- t := 0; px := x + mem[wi + i] * D; py := y + mem[wj + i]; s := 0
  (focus
     ((first
         | refine Light.Ends.seqSelf ?_
         | refine Light.Ends.skipLast ?_);
       (repeat
           with_unfolding_none
             first
             | refine Light.Ends.seqAssoc ?_
             | refine Light.Ends.skipThen ?_))
     (refine Light.Ends.setToThen 0 ?_ ?_ ?_)
     (on_goal -1 =>
         first
         | ( (simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost, List.map_cons,
                 List.map_nil, List.sum_cons, List.sum_nil, ])
             (first
               | omega
               | ((ring_nf); (omega))))
         | omega
         |
           (simp [] <;>
               first
               | omega
               | ((ring_nf); (omega))))
     (on_goal -1 =>
         try have := Light.Std.space_le (by assumption)
         try have := Light.Std.const_le (by assumption)
         simp [Light.Limits.Addr, abs_le, -abs_mul] <;> omega)
     (try with_unfolding_none refine Light.Ends.skip ?_))
  (focus
     ((first
         | refine Light.Ends.seqSelf ?_
         | refine Light.Ends.skipLast ?_);
       (repeat
           with_unfolding_none
             first
             | refine Light.Ends.seqAssoc ?_
             | refine Light.Ends.skipThen ?_))
     (refine Light.Ends.setToThen (x.x + thinI x i * x.D : ℕ) ?_ ?_ ?_)
     (on_goal -1 =>
         first
         | ( (simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost, List.map_cons,
                 List.map_nil, List.sum_cons, List.sum_nil, rIcast])
             (first
               | omega
               | ((ring_nf); (omega))))
         | omega
         |
            (simp [rIcast] <;>
               first
               | omega
               | ((ring_nf); (omega))))
     (on_goal -1 =>
         try have := Light.Std.space_le (by assumption)
         try have := Light.Std.const_le (by assumption)
         simp [Light.Limits.Addr, abs_le, -abs_mul, rIcast] <;> omega)
     (try with_unfolding_none refine Light.Ends.skip ?_))
  (focus
     ((first
         | refine Light.Ends.seqSelf ?_
         | refine Light.Ends.skipLast ?_);
       (repeat
           with_unfolding_none
             first
             | refine Light.Ends.seqAssoc ?_
             | refine Light.Ends.skipThen ?_))
     (refine Light.Ends.setToThen (x.y + thinJ x i : ℕ) ?_ ?_ ?_)
     (on_goal -1 =>
         first
         | ( (simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost, List.map_cons,
                 List.map_nil, List.sum_cons, List.sum_nil, rJcast])
             (first
               | omega
               | ((ring_nf); (omega))))
         | omega
         |
            (simp [rJcast] <;>
               first
               | omega
               | ((ring_nf); (omega))))
     (on_goal -1 =>
          try have := Light.Std.space_le (by assumption)
          try have := Light.Std.const_le (by assumption)
          simp [Light.Limits.Addr, abs_le, -abs_mul, rJcast] <;> omega)
     (try with_unfolding_none refine Light.Ends.skip ?_))
  (focus
     ((first
         | refine Light.Ends.seqSelf ?_
         | refine Light.Ends.skipLast ?_);
       (repeat
           with_unfolding_none
             first
             | refine Light.Ends.seqAssoc ?_
             | refine Light.Ends.skipThen ?_))
     (refine
         Light.Ends.setToThen
           0
             -- the inner product
             
           ?_ ?_ ?_)
     (on_goal -1 =>
         first
         | ( (simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost, List.map_cons,
                 List.map_nil, List.sum_cons, List.sum_nil, ])
             (first
               | omega
               | ((ring_nf); (omega))))
         | omega
         |
           (simp [] <;>
               first
               | omega
               | ((ring_nf); (omega))))
     (on_goal -1 =>
          try have := Light.Std.space_le (by assumption)
          try have := Light.Std.const_le (by assumption)
          simp [Light.Limits.Addr, abs_le, -abs_mul] <;> omega)
     (try with_unfolding_none refine Light.Ends.skip ?_))
  -- the inner product
  refine Ends.next (24 * x.D + 4) ((bruteInner_spec std x (i := i) segX segY hpre.lenX hpre.lenY
    hpre.leX hpre.leY hI hJ (by omega) (by omega) hword).mono le_rfl ?_) (by
      simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      first | omega | (ring_nf; omega))
  rintro _ rfl
  unfold bruteLocs
  -- mem[out + i] := s; i := i + 1
  (focus
     ((first
         | refine Light.Ends.seqSelf ?_
         | refine Light.Ends.skipLast ?_);
       (repeat
           with_unfolding_none
             first
             | refine Light.Ends.seqAssoc ?_
             | refine Light.Ends.skipThen ?_))
     (refine
         Light.Ends.storeToThen (x.out + i) (brutePartial x.N x.D x.X x.Y (thinI x i) (thinJ x i) x.D)
           ?_ ?_ ?_)
     (on_goal -1 =>
         first
         | ( (simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost, List.map_cons,
                 List.map_nil, List.sum_cons, List.sum_nil, ])
             (first
               | omega
               | ((ring_nf); (omega))))
         | omega
         |
           (simp [] <;>
               first
               | omega
               | ((ring_nf); (omega))))
     (on_goal -1 =>
         try have := Light.Std.space_le (by assumption)
         try have := Light.Std.const_le (by assumption)
         simp [Light.Limits.Addr, abs_le, -abs_mul] <;> omega)
     (try with_unfolding_none refine Light.Ends.skip ?_))
  (focus
     ((first
         | refine Light.Ends.seqSelf ?_
         | refine Light.Ends.skipLast ?_);
       (repeat
           with_unfolding_none
             first
             | refine Light.Ends.seqAssoc ?_
             | refine Light.Ends.skipThen ?_))
     (refine Light.Ends.setToThen (i + 1 : ℕ) ?_ ?_ ?_)
     (on_goal -1 =>
         first
         | ( (simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost, List.map_cons,
                 List.map_nil, List.sum_cons, List.sum_nil, ])
             (first
               | omega
               | ((ring_nf); (omega))))
         | omega
         |
           (simp [] <;>
               first
               | omega
               | ((ring_nf); (omega))))
     (on_goal -1 =>
         try have := Light.Std.space_le (by assumption)
         try have := Light.Std.const_le (by assumption)
         simp [Light.Limits.Addr, abs_le, -abs_mul] <;> omega)
     (try with_unfolding_none refine Light.Ends.skip ?_))
  refine ⟨_, _, _, _, _, rfl, fun j hj => ?_, ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
  · rw [Function.update_of_ne (by omega)]
    exact hdone j hlt
  · rw [Function.update_self]
    rfl
  · intro a ha
    change Function.update μ' (x.out + i) _ a = μ a
    rw [Function.update_of_ne (by
      intro heq
      rcases ha with hlt | hge <;> omega)]
    exact hfr a (by rcases ha with hlt | hge <;> omega)

/-- **The brute force is right on every instance** for which D U² fits in a word.  It needs N + 1
cells above the free pointer only as room for addresses that are formed and never used. -/
theorem thinBrute_spec (std : Std lim) (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ) (u : ℤ)
    (hpre : x.Pre μ fr) (hsp : fr + x.N + 1 ≤ lim.space)
    (hword : ((x.D * (x.U * x.U) : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d thinBruteBody
      ⟨Light.frame [(x.N : ℤ), (x.D : ℤ), (x.w : ℤ), u, (x.x : ℤ), (x.y : ℤ), (x.wi : ℤ), (x.wj : ℤ),
        (x.out : ℤ), (fr : ℤ)], μ⟩
      (40 * ((x.w + 1) * (x.D + 1))) fun σ' => thinTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  unfold thinBruteBody
  refine Ends.whileConst (BruteInv x μ u fr) x.w (24 * x.D + 33) ?start ?round ?done ?time
  case start =>
    exact ⟨0, 0, 0, 0, μ, by rw [← frame_append_zeros _ 5]; rfl, fun j hj => absurd hj (by omega),
      SameOutside.refl⟩
  case round =>
    intro i σ hi h
    refine ⟨?_, ?_, bruteRound_spec std hpre hsp hword hi h⟩ <;>
      obtain ⟨t, px, py, s, μ', rfl, -, -⟩ := h
    · simp
    · simpa [bruteLocs] using hi
  case done =>
    rintro _ ⟨t, px, py, s, μ', rfl, hdone, hfr⟩
    refine ⟨by simp, by simp [bruteLocs], fun i hi => ?_, fun a ha => hfr a ha.2⟩
    have hi' : i < x.w := by rwa [Light.Sec2.length_thinOut hpre] at hi
    change μ' (x.out + i) = _
    rw [hdone i hi', ← getD_thinOut hpre hi', List.getD_eq_getElem _ _ hi]
  case time =>
    have hleft : x.w * (4 + (24 * x.D + 33)) = 24 * (x.w * x.D) + 37 * x.w := by ring
    have hright : (x.w + 1) * (x.D + 1) = x.w * x.D + x.w + x.D + 1 := by ring
    simp
    omega

end Light.Sec2

namespace Light.Sec4
open ThreeSumApsp

theorem pruned_program_thinBrute_lookup (G : RatParams) :
    (program31P G)[Sec2.pThinBrute]? = some Sec2.thinBruteBody := by rfl

theorem pruned_program_thinBrute_meets (G : RatParams) (R : Program)
    (lim : Limits) (d : ℕ) (std : Std lim)
    (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ)
    (hpre : x.Pre μ fr) (hsp : fr + x.N + 1 ≤ lim.space)
    (hword : ((x.D * (x.U * x.U) : ℕ) : ℤ) ≤ lim.word) :
    Meets lim (program31P G ++ R) Sec2.pThinBrute (d + 1)
      [x.N,x.D,x.w,x.U,x.x,x.y,x.wi,x.wj,x.out,fr] μ
      (40 * ((x.w + 1) * (x.D + 1)))
      (fun r μ' => lopCountTask.Post x μ fr r μ') := by
  refine ⟨Sec2.thinBruteBody, ?_, ?_⟩
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp (pruned_program_thinBrute_lookup G)).1]
    exact pruned_program_thinBrute_lookup G
  · exact Sec2.thinBrute_spec std x μ fr x.U hpre hsp hword

end Light.Sec4

namespace ThreeSumSharpTail

open Light Light.Sec4 ThreeSumApsp ThreeSumApsp.Spec

noncomputable def regimeTest (A B : ℕ) : Stmt :=
  Classical.choose (ThreeSumSharpTailRationalRegimeTest.rationalRegimeTest_solver A B)

noncomputable def regimeTestSteps (A B : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (ThreeSumSharpTailRationalRegimeTest.rationalRegimeTest_solver A B))

theorem regimeTest_spec (A B : ℕ) :
    ∀ (lim : Limits) (P : Program) (d N D : ℕ) (μ : ℕ → ℤ),
      1 ≤ N → 1 ≤ D → ((N ^ A + D ^ B + 100 : ℕ) : ℤ) ≤ lim.word →
      Ends lim P d (regimeTest A B) ⟨Light.frame [N, D], μ⟩ (regimeTestSteps A B)
        (fun σ => σ.mem = μ ∧
          ((σ.loc 0 = 1 ∧ D ^ B ≤ N ^ A) ∨ (σ.loc 0 = 0 ∧ N ^ A < D ^ B))) :=
  Classical.choose_spec (Classical.choose_spec (ThreeSumSharpTailRationalRegimeTest.rationalRegimeTest_solver A B))

noncomputable def rationalRegimeWrapper (A B : ℕ) : Stmt :=
  .seq (.call (Proc.offline32 + 6) [v 0, v 1] 10)
    (.ite (.eq (v 10) (k 1))
      (.call Proc.offline32 [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] 0)
      (.call Sec2.pThinBrute [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] 0))

def rationalRegimeTestCall (A B : ℕ) : Stmt :=
  .call (Proc.offline32 + 6) [v 0, v 1] 10

def rationalRegimeBody (A B : ℕ) : Stmt :=
  .seq (rationalRegimeTestCall A B)
    (.ite (.eq (v 10) (k 1))
      (.call Proc.offline32 [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] 0)
      (.call Sec2.pThinBrute [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] 0))

noncomputable def rationalRegimeProgram (G : RatParams) (A B : ℕ) : Program :=
  program31P G ++ [regimeTest A B, rationalRegimeBody A B]

def rationalRegimeTestIndex (G : RatParams) : ℕ := (program31P G).length

def rationalRegimeWrapperIndex (G : RatParams) : ℕ := (program31P G).length + 1

noncomputable def rationalRegimeCountTime (G : RatParams) (A B : ℕ) (ps : List ℕ) : ℕ :=
  regimeTestSteps A B + 20 +
    (if (ps.getD 1 0) ^ B ≤ (ps.getD 0 0) ^ A then
      tOffline32P cShared30 G (ps.getD 0 0) (ps.getD 1 0) (ps.getD 2 0)
    else 40 * ((ps.getD 2 0 + 1) * (ps.getD 1 0 + 1)))

noncomputable def rationalRegimeCountNeed (A B : ℕ) (need : List ℕ → Need) :
    List ℕ → Need := fun ps =>
  ⟨(need (ps ++ [1])).word + (ps.getD 0 0) ^ A + (ps.getD 1 0) ^ B + ps.getD 1 0 + 100,
    (need (ps ++ [1])).cells + ps.getD 0 0 + 1, (need (ps ++ [1])).depth + 1⟩

theorem rational_getD_succ_le_prod (ps : List ℕ) (i : ℕ) :
    ps.getD i 0 + 1 ≤ (ps.map (· + 1)).prod := by
  have hpos : ∀ n ∈ ps.map (· + 1), (1 : ℕ) ≤ n := by
    intro n hn
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp hn
    omega
  by_cases hi : i < ps.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.single_le_prod hpos _ (List.mem_map.mpr ⟨ps[i], List.getElem_mem hi, rfl⟩)
  · rw [List.getD_eq_default _ _ (by omega)]
    simpa using List.one_le_prod_of_one_le hpos

theorem rationalRegimeCountNeed_poly (A B : ℕ) {need : List ℕ → Need}
    (hneed : PolyNeedN need) : PolyNeedN (rationalRegimeCountNeed A B need) := by
  obtain ⟨s, k, hpoly⟩ := hneed
  refine ⟨s + k + 7, k + A + B + 1, fun ps => ?_⟩
  obtain ⟨hw, hc, hd⟩ := hpoly (ps ++ [1])
  have hN := rational_getD_succ_le_prod ps 0
  have hD := rational_getD_succ_le_prod ps 1
  have hpos : 1 ≤ (ps.map (· + 1)).prod :=
    List.one_le_prod_of_one_le (by simp)
  have hb : polyBound s k (ps ++ [1]) =
      2 ^ (s + k) * (ps.map (· + 1)).prod ^ k := by
    simp [polyBound, List.map_append, List.prod_append, mul_pow, pow_add]
    ring
  rw [hb] at hw hc hd
  generalize hqdef : (ps.map (· + 1)).prod = q at *
  let K := k + A + B + 1
  have hq : 0 < q := by omega
  have hq1 : 1 ≤ q := by omega
  have hk : q ^ k ≤ q ^ K := Nat.pow_le_pow_right hq (by dsimp [K]; omega)
  have hNpow : (ps.getD 0 0) ^ A ≤ q ^ K :=
    (Nat.pow_le_pow_left (by omega) A).trans
      (Nat.pow_le_pow_right hq (by dsimp [K]; omega))
  have hDpow : (ps.getD 1 0) ^ B ≤ q ^ K :=
    (Nat.pow_le_pow_left (by omega) B).trans
      (Nat.pow_le_pow_right hq (by dsimp [K]; omega))
  have hqpow : q ≤ q ^ K := by
    have h := Nat.pow_le_pow_right hq (show 1 ≤ K by dsimp [K]; omega)
    simpa using h
  have hpow1 : 1 ≤ q ^ K := Nat.one_le_pow _ _ hq
  have hcoef : 1 ≤ 2 ^ (s + k) := Nat.one_le_pow _ _ (by decide)
  have hbase : q ^ K ≤ 2 ^ (s + k) * q ^ K := Nat.le_mul_of_pos_left _ (by omega)
  have hW := hw.trans (Nat.mul_le_mul_left (2 ^ (s + k)) hk)
  have hC := hc.trans (Nat.mul_le_mul_left (2 ^ (s + k)) hk)
  have hDep := hd.trans (Nat.mul_le_mul_left (2 ^ (s + k)) hk)
  have hNp := hNpow.trans hbase
  have hDp := hDpow.trans hbase
  have hNl : ps.getD 0 0 ≤ 2 ^ (s + k) * q ^ K := (show ps.getD 0 0 ≤ q by omega).trans (hqpow.trans hbase)
  have hDl : ps.getD 1 0 ≤ 2 ^ (s + k) * q ^ K := (show ps.getD 1 0 ≤ q by omega).trans (hqpow.trans hbase)
  have hZ1 := hpow1.trans hbase
  have htarget : polyBound (s + k + 7) K ps =
      128 * (2 ^ (s + k) * q ^ K) := by
    simp only [polyBound, hqdef]
    rw [show s + k + 7 = (s + k) + 7 by omega, pow_add]
    norm_num
    ring
  change (rationalRegimeCountNeed A B need ps).word ≤ polyBound (s + k + 7) K ps ∧
    (rationalRegimeCountNeed A B need ps).cells ≤ polyBound (s + k + 7) K ps ∧
    (rationalRegimeCountNeed A B need ps).depth ≤ polyBound (s + k + 7) K ps
  rw [htarget]
  generalize hz : 2 ^ (s + k) * q ^ K = Z at *
  simp only [rationalRegimeCountNeed]
  constructor
  · omega
  · constructor <;> omega

theorem rationalRegimeCount_base_ok (A B : ℕ) {need : List ℕ → Need}
    {N D w fr d : ℕ} {lim : Limits}
    (hok : (rationalRegimeCountNeed A B need [N, D, w]).Ok lim fr d) :
    (need ([N, D, w] ++ [1])).Ok lim fr (d + 1) := by
  refine ⟨?_, ?_, hok.space, ?_⟩
  · have h := hok.word
    simp only [rationalRegimeCountNeed, Nat.cast_add] at h
    omega
  · have h := hok.cells
    simp only [rationalRegimeCountNeed] at h
    omega
  · have h := hok.depth
    simp only [rationalRegimeCountNeed] at h
    omega

theorem rationalRegimeCount_test_word (A B : ℕ) {need : List ℕ → Need}
    {N D w fr d : ℕ} {lim : Limits}
    (hok : (rationalRegimeCountNeed A B need [N, D, w]).Ok lim fr d) :
    ((N ^ A + D ^ B + 100 : ℕ) : ℤ) ≤ lim.word := by
  have hn : N ^ A + D ^ B + 100 ≤
      (rationalRegimeCountNeed A B need [N, D, w]).word := by
    simp [rationalRegimeCountNeed]
    omega
  exact (show ((N ^ A + D ^ B + 100 : ℕ) : ℤ) ≤
    ((rationalRegimeCountNeed A B need [N, D, w]).word : ℤ) by exact_mod_cast hn).trans hok.word

theorem rationalRegimeCount_std (A B : ℕ) {need : List ℕ → Need}
    {N D w fr d : ℕ} {lim : Limits}
    (hok : (rationalRegimeCountNeed A B need [N, D, w]).Ok lim fr d) : Std lim := by
  refine ⟨hok.space, ?_⟩
  have hword := hok.word
  have hn : 100 ≤ (rationalRegimeCountNeed A B need [N,D,w]).word := by
    simp [rationalRegimeCountNeed] <;> omega
  exact (show (100 : ℤ) ≤ ((rationalRegimeCountNeed A B need [N,D,w]).word : ℤ) by exact_mod_cast hn).trans hword

theorem rationalRegimeCount_brute_space (A B : ℕ) {need : List ℕ → Need}
    {N D w fr d : ℕ} {lim : Limits}
    (hok : (rationalRegimeCountNeed A B need [N, D, w]).Ok lim fr d) : fr + N + 1 ≤ lim.space := by
  have h := hok.cells
  simp only [rationalRegimeCountNeed, List.getD_cons_zero] at h
  omega

theorem rationalRegimeCount_brute_word (A B : ℕ) {need : List ℕ → Need}
    {N D w fr d : ℕ} {lim : Limits}
    (hok : (rationalRegimeCountNeed A B need [N, D, w]).Ok lim fr d) : (D : ℤ) ≤ lim.word := by
  have h := hok.word
  have hn : D ≤ (rationalRegimeCountNeed A B need [N,D,w]).word := by
    simp [rationalRegimeCountNeed]
    omega
  exact (show (D : ℤ) ≤ ((rationalRegimeCountNeed A B need [N,D,w]).word : ℤ) by exact_mod_cast hn).trans h

theorem rationalRegimeCount_call_depth (A B : ℕ) {need : List ℕ → Need}
    {N D w fr d : ℕ} {lim : Limits}
    (hok : (rationalRegimeCountNeed A B need [N, D, w]).Ok lim fr d) : d + 1 ≤ lim.depth := by
  have h := hok.depth
  simp only [rationalRegimeCountNeed] at h
  omega

theorem rationalRegime_count_solves (G : RatParams) (a s : ℚ) (A B : ℕ) (C : ℝ)
    (hC : 0 ≤ C)
    (hcost : ∀ N D : ℕ, 1 ≤ D → (D : ℝ) ≤ (N : ℝ) ^ (a : ℝ) →
      CostsWithinP G C N D
        ((N : ℝ) ^ 2 * (Real.log D + 1) ^ 2 / (D : ℝ) ^ (s : ℝ))
        ((D : ℝ) ^ (1 / 2 - (s : ℝ)) * (Real.log D + 1)))
    (heq : ∀ N D : ℕ, 1 ≤ N → 1 ≤ D →
      ((D : ℝ) ≤ (N : ℝ) ^ (a : ℝ) ↔ D ^ B ≤ N ^ A)) :
    ∃ need : List ℕ → Need, PolyNeedN need ∧
      SolvesN lopCountTask (rationalRegimeProgram G A B) (rationalRegimeWrapperIndex G)
        (rationalRegimeCountTime G A B) (rationalRegimeCountNeed A B need) := by
  obtain ⟨baseNeed, hbaseNeed, hbaseSol⟩ := ThreeSumSharpTail.pruned_program_solves G
  refine ⟨baseNeed, hbaseNeed, ?_⟩
  refine ⟨rationalRegimeBody A B, ?_, ?_⟩
  · simp [rationalRegimeProgram, rationalRegimeWrapperIndex]
  · intro R lim d x μ fr hpre hok
    have hpre0 := hpre
    obtain ⟨hx, hzero, hU⟩ := hpre
    have hstd : Std lim := rationalRegimeCount_std A B hok
    have htestWord := rationalRegimeCount_test_word A B hok
    have hspace := rationalRegimeCount_brute_space A B hok
    have hwordD := rationalRegimeCount_brute_word A B hok
    have hbaseOk := rationalRegimeCount_base_ok A B (need := baseNeed) hok
    have hbaseOk' : (baseNeed [x.N, x.D, x.w, x.U]).Ok lim fr d := by
      have hbaseAtD : (baseNeed ([x.N, x.D, x.w] ++ [1])).Ok lim fr d := by
        exact hbaseOk.mono le_rfl le_rfl (by omega)
      simpa [hU] using hbaseAtD
    have hdepth : d < lim.depth := by
      have hd := rationalRegimeCount_call_depth A B hok
      omega
    have hfrLim : fr ≤ lim.space := by omega
    have htestIndex :
        (rationalRegimeProgram G A B)[rationalRegimeTestIndex G]? =
          some (regimeTest A B) := by
      simp [rationalRegimeProgram, rationalRegimeTestIndex]
    have htest : Meets lim (rationalRegimeProgram G A B ++ R)
        (rationalRegimeTestIndex G) (d + 1) [x.N, x.D] μ
        (regimeTestSteps A B)
        (fun r μ' => μ' = μ ∧
          ((r = 1 ∧ x.D ^ B ≤ x.N ^ A) ∨ (r = 0 ∧ x.N ^ A < x.D ^ B))) := by
      refine ⟨regimeTest A B, ?_, ?_⟩
      · simp [rationalRegimeProgram, rationalRegimeTestIndex]
      · simpa using regimeTest_spec A B lim (rationalRegimeProgram G A B ++ R)
          (d + 1) x.N x.D μ hx.N_pos hx.D_pos htestWord
    let tp : ℝ := (x.N : ℝ) ^ 2 * (Real.log x.D + 1) ^ 2 /
      (x.D : ℝ) ^ (s : ℝ)
    let tq : ℝ := (x.D : ℝ) ^ (1 / 2 - (s : ℝ)) * (Real.log x.D + 1)
    have hregime :
        ∀ {r : ℤ}, r = 1 → x.D ^ B ≤ x.N ^ A →
          CostsWithinP G C x.N x.D tp tq := by
      intro r hr hnat
      apply hcost x.N x.D hx.D_pos
      exact (heq x.N x.D hx.N_pos hx.D_pos).2 hnat
    have hbaseOffline :
        ∀ {r : ℤ}, r = 1 → x.D ^ B ≤ x.N ^ A →
          Meets lim (rationalRegimeProgram G A B ++ R) Proc.offline32 (d + 1)
            [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ
            (tOffline32P cShared30 G x.N x.D x.w)
            (fun r μ' => lopCountTask.Post x μ fr r μ') := by
      intro r hr hnat
      have hc := hregime hr hnat
      have hm := hbaseSol ([regimeTest A B, rationalRegimeBody A B] ++ R)
        lim fr d x μ C tp tq hC hpre0 hc hbaseOk'
      simpa [rationalRegimeProgram, List.append_assoc] using hm
    have hbaseBrute :
        Meets lim (rationalRegimeProgram G A B ++ R) Sec2.pThinBrute (d + 1)
          [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ
          (40 * ((x.w + 1) * (x.D + 1)))
          (fun r μ' => lopCountTask.Post x μ fr r μ') := by
      have hwordBrute : ((x.D * (x.U * x.U) : ℕ) : ℤ) ≤ lim.word := by
        simpa [hU] using hwordD
      have hm := Light.Sec4.pruned_program_thinBrute_meets G
        ([regimeTest A B, rationalRegimeBody A B] ++ R) lim d hstd x μ fr hx hspace hwordBrute
      simpa [rationalRegimeProgram, List.append_assoc] using hm
    have hBody : Ends lim (rationalRegimeProgram G A B ++ R) d
        (rationalRegimeBody A B)
        ⟨frame [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr], μ⟩
        (rationalRegimeCountTime G A B [x.N, x.D, x.w])
        (fun σ => lopCountTask.Post x μ fr (σ.loc 0) σ.mem) := by
      refine Ends.callToThen htest ?_ ?_ hdepth ?_
      · intro r μ' hres
        rcases hres with ⟨hμ, hregimeResult⟩
        subst μ'
        let Tbranch := if x.D ^ B ≤ x.N ^ A then
          tOffline32P cShared30 G x.N x.D x.w
          else 40 * ((x.w + 1) * (x.D + 1))
        change Ends lim (rationalRegimeProgram G A B ++ R) d
          (.ite (Cond.eq (v 10) (k 1))
            (.call Proc.offline32 [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] 0)
            (.call Sec2.pThinBrute [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] 0))
          ⟨frame (setLocal [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] 10 r), μ⟩
          (rationalRegimeCountTime G A B [x.N, x.D, x.w] -
            (([v 0, v 1].map Expr.cost).sum + 2 + regimeTestSteps A B))
          (fun σ => lopCountTask.Post x μ fr (σ.loc 0) σ.mem)
        have hrword : |r| ≤ lim.word := by
          rcases hregimeResult with ⟨hr, _⟩ | ⟨hr, _⟩
          · subst r
            have h100 := hstd.const_le
            have h1 : (1 : ℤ) ≤ lim.word := by omega
            simpa
          · subst r
            exact le_trans (by norm_num) hstd.const_le
        have hcnd : (Cond.eq (v 10) (k 1)).Safe lim
            ⟨frame (setLocal [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] 10 r), μ⟩ := by
          have := hstd.const_le
          have h1 : (1 : ℤ) ≤ lim.word := by omega
          simp [Light.Cond.Safe, Light.Expr.Safe, Light.Limits.Addr, abs_le, -abs_mul]
            <;> omega
        have hbranchDepth := hdepth
        have hite : Ends lim (rationalRegimeProgram G A B ++ R) d
            (.ite (Cond.eq (v 10) (k 1))
              (.call Proc.offline32 [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] 0)
              (.call Sec2.pThinBrute [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] 0))
            ⟨frame (setLocal [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] 10 r), μ⟩
            (16 + Tbranch)
            (fun σ => lopCountTask.Post x μ fr (σ.loc 0) σ.mem) := by
          refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) hcnd ?_
          · have hnat : x.D ^ B ≤ x.N ^ A := by
              rcases hregimeResult with h | h
              · exact h.2
              · have : (Cond.eq (v 10) (k 1)).Holds
                    ⟨frame (setLocal [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] 10 r), μ⟩ := hc
                simp [Light.Cond.Holds, Light.Expr.val, Light.frame_setLocal] at this
                omega
            have hoff := hbaseOffline rfl hnat
            have hsa :
                (∀ e ∈ [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9],
                  e.Safe lim ⟨frame (setLocal [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] 10 r), μ⟩) ∧
                  ([v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9].map
                    (·.val ⟨frame (setLocal [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] 10 r), μ⟩) =
                      [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr]) := by
              constructor
              · have hs := Light.Sec2.thinFrame_args_safe lim x μ fr r hstd hx hfrLim hU hrword
                simpa [Light.Sec2.thinFrameArgs, Light.Sec2.thinFrameState,
                  Light.Sec2.thinFrameLocs, Light.frame_setLocal, Light.frame] using hs
              · have hv := Light.Sec2.thinFrame_args_vals lim x μ fr r hstd hx hfrLim hU hrword
                simpa [Light.Sec2.thinFrameArgs, Light.Sec2.thinFrameState,
                  Light.Sec2.thinFrameLocs, Light.frame_setLocal, Light.frame] using hv
            exact Ends.callTo hoff (fun r μ' hr => by
              simpa [lopCountTask, Function.update] using hr) hsa hdepth
              (by simp [Tbranch, hnat, Light.Expr.cost]; omega)
          · have hnat : x.N ^ A < x.D ^ B := by
              rcases hregimeResult with h | h
              · have : ¬ (Cond.eq (v 10) (k 1)).Holds
                    ⟨frame (setLocal [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] 10 r), μ⟩ := hc
                simp [Light.Cond.Holds, Light.Expr.val, Light.frame_setLocal] at this
                omega
              · exact h.2
            have hbr := hbaseBrute
            have hsa :
                (∀ e ∈ [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9],
                  e.Safe lim ⟨frame (setLocal [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] 10 r), μ⟩) ∧
                  ([v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9].map
                    (·.val ⟨frame (setLocal [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] 10 r), μ⟩) =
                      [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr]) := by
              constructor
              · have hs := Light.Sec2.thinFrame_args_safe lim x μ fr r hstd hx hfrLim hU hrword
                simpa [Light.Sec2.thinFrameArgs, Light.Sec2.thinFrameState,
                  Light.Sec2.thinFrameLocs, Light.frame_setLocal, Light.frame] using hs
              · have hv := Light.Sec2.thinFrame_args_vals lim x μ fr r hstd hx hfrLim hU hrword
                simpa [Light.Sec2.thinFrameArgs, Light.Sec2.thinFrameState,
                  Light.Sec2.thinFrameLocs, Light.frame_setLocal, Light.frame] using hv
            exact Ends.callTo hbr (fun r μ' hr => by
              simpa [lopCountTask, Function.update] using hr) hsa hdepth
              (by simp [Tbranch, Nat.not_le_of_gt hnat, Light.Expr.cost]; omega)
          · simp [Light.Cond.cost, Light.Expr.cost]
            omega
        have hbranchTime : rationalRegimeCountTime G A B [x.N, x.D, x.w] -
            (([v 0, v 1].map Expr.cost).sum + 2 + regimeTestSteps A B) = 16 + Tbranch := by
          simp [rationalRegimeCountTime, Tbranch, Light.Expr.cost, regimeTestSteps]
          omega
        rw [hbranchTime]
        exact hite
      · constructor
        · have hsafe := Light.Sec2.thinFrame_args01_safe lim x μ fr 0 hstd hx hfrLim hU
            (le_trans (by norm_num) hstd.const_le)
          simpa [Light.Sec2.thinFrameArgs01, Light.Sec2.thinFrameState,
            Light.Sec2.thinFrameLocs, Light.frame_setLocal, Light.frame] using hsafe
        · have hvals := Light.Sec2.thinFrame_args01_vals lim x μ fr 0 hstd hx hfrLim hU
            (le_trans (by norm_num) hstd.const_le)
          simpa [Light.Sec2.thinFrameArgs01, Light.Sec2.thinFrameState,
            Light.Sec2.thinFrameLocs, Light.frame_setLocal, Light.frame] using hvals
      · simp [rationalRegimeCountTime, List.getD_cons_zero, List.getD_cons_succ,
          Light.Expr.cost]
        omega
    simpa [lopCountTask, rationalRegimeBody, rationalRegimeTestCall,
      rationalRegimeCountTime] using hBody

end ThreeSumSharpTail

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

namespace LopHosts

theorem rational_lop_length_thinOut (N D : ℕ) (X Y : List ℤ) {WI WJ : List ℕ} {w : ℕ}
    (h1 : WI.length = w) (h2 : WJ.length = w) :
    (thinOut N D X Y WI WJ).length = w := by
  simp [thinOut, h1, h2]

theorem rational_lop_detect_spec {P₀ R : Program} {p : ℕ} {Tn : List ℕ → ℕ}
    {need : List ℕ → Need} (hsol : SolvesN lopCountTask P₀ p Tn need)
    {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : lopDetectTask.Pre x μ fr)
    (hok : (lopDetectNeed need (lopDetectTask.pars x)).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (lopDetectBody p)
      ⟨Light.frame (lopDetectTask.args x ++ [(fr : ℤ)]), μ⟩
      (lopDetectTime Tn (lopDetectTask.pars x))
      (fun σ' => lopDetectTask.Post x μ fr (σ'.loc 0) σ'.mem) := by
  have hdep : d + ((need [x.N, x.D, x.w]).depth + 1) ≤ lim.depth := hok.depth
  have hpreCount : lopCountTask.Pre x μ fr := ⟨hpre.1, hpre.2.1, hpre.2.2⟩
  have hlen := rational_lop_length_thinOut x.N x.D x.X x.Y hpre.1.lenWI hpre.1.lenWJ
  have hfr : (fr : ℤ) ≤ lim.word := by
    have hfrSpace : fr ≤ lim.space := by have hc := hok.cells; omega
    have hcast : (fr : ℤ) ≤ (lim.space : ℤ) := by exact_mod_cast hfrSpace
    exact hcast.trans hok.space
  have hwordx : (x.w : ℤ) ≤ lim.word := by
    have hxf : x.w ≤ fr := by have := hpre.1.belowOut; omega
    have hcast : (x.w : ℤ) ≤ (fr : ℤ) := by exact_mod_cast hxf
    exact hcast.trans hfr
  have hm : Meets lim (P₀ ++ R) p (d + 1)
      [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ
      (Tn [x.N, x.D, x.w]) (fun _ μ₁ =>
        Seg μ₁ x.out (thinOut x.N x.D x.X x.Y x.WI x.WJ) ∧
        KeptBut μ μ₁ fr x.out x.w) := by
    have hokCount : (need [x.N, x.D, x.w]).Ok lim fr (d + 1) := by
      refine hok.mono le_rfl le_rfl ?_
      change d + 1 + (need [x.N, x.D, x.w]).depth ≤
        d + ((need [x.N, x.D, x.w]).depth + 1)
      omega
    exact hsol.meets R x hpreCount hokCount
  change Ends lim (P₀ ++ R) d (lopDetectBody p)
    ⟨Light.frame [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr], μ⟩
    (Tn [x.N, x.D, x.w] + 20 * x.w + 18) _
  refine Ends.callToThen (p:=p) (args:=[v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9])
    (x:=10) (s:=.for 10 (v 2)
      (.ite (Light.Cond.eq (M ((Light.Expr.op Light.Op.add) (v 8) (v 10))) (k 0)) .skip
        (.store ((Light.Expr.op Light.Op.add) (v 8) (v 10)) (k 1))))
    (vals:=[x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr])
    (T':=Tn [x.N, x.D, x.w]) (R:=fun _ μ₁ =>
      Seg μ₁ x.out (thinOut x.N x.D x.X x.Y x.WI x.WJ) ∧ KeptBut μ μ₁ fr x.out x.w)
    hm (fun r μ₁ hR => ?_) ?_ ?_ ?_
  rcases hR with ⟨hseg, hk⟩
  let f : ℕ → ℤ := fun i => if μ₁ (x.out + i) = 0 then 0 else 1
  have hf : ∀ i, f i = if μ₁ (x.out + i) = 0 then 0 else 1 := by intro i; rfl
  refine Ends.forFrame (fun j μ' => μ' = wrote μ₁ x.out f j) x.w wrote_zero.symm ?round ?done
    (hT := by simp; omega)
  ·
    rintro j _ hj rfl
    have hread : wrote μ₁ x.out f j (x.out + j) = μ₁ (x.out + j) := wrote_rest (by omega)
    have hfrSpace : fr ≤ lim.space := by have h := hok.cells; omega
    have hbelowOut : x.out + x.w ≤ fr := hpre.1.belowOut
    have haddrNat : x.out + j < lim.space := by omega
    have hsumWord : (x.out + j : ℤ) ≤ lim.word := by
      have hn : x.out + j ≤ fr := by omega
      have hnZ : (x.out + j : ℤ) ≤ (fr : ℤ) := by exact_mod_cast hn
      exact hnZ.trans hfr
    have hwordOne : (1 : ℤ) ≤ lim.word := by
      have hn : 1 ≤ x.w := by omega
      have hnZ : (1 : ℤ) ≤ (x.w : ℤ) := by exact_mod_cast hn
      exact hnZ.trans hwordx
    have hOpSafe :
        (Light.Expr.op Light.Op.add (v 8) (v 10)).Safe lim
          ⟨Light.frame (Light.setLocal (Light.setLocal [↑x.N, ↑x.D, ↑x.w, ↑x.U, ↑x.x, ↑x.y, ↑x.wi, ↑x.wj, ↑x.out, ↑fr] 10 r) 10 j), wrote μ₁ x.out f j⟩ := by
      simp only [Light.Expr.Safe, Light.Expr.val, Light.Op.eval]
      constructor
      · trivial
      · constructor
        · trivial
        · have hv :
              (Light.Op.add.eval ((v 8).val ⟨Light.frame (Light.setLocal (Light.setLocal [↑x.N, ↑x.D, ↑x.w, ↑x.U, ↑x.x, ↑x.y, ↑x.wi, ↑x.wj, ↑x.out, ↑fr] 10 r) 10 j),
                wrote μ₁ x.out f j⟩) ((v 10).val ⟨Light.frame (Light.setLocal (Light.setLocal [↑x.N, ↑x.D, ↑x.w, ↑x.U, ↑x.x, ↑x.y, ↑x.wi, ↑x.wj, ↑x.out, ↑fr] 10 r) 10 j),
                wrote μ₁ x.out f j⟩)) = (x.out + j : ℤ) := by
            simp [Light.Expr.val, Light.Op.eval, Light.frame, Light.setLocal]
          simp [Light.frame, Light.setLocal]
          rw [abs_of_nonneg (by positivity)]
          exact hsumWord
    have hLoadSafe :
        (M (Light.Expr.op Light.Op.add (v 8) (v 10))).Safe lim
          ⟨Light.frame (Light.setLocal (Light.setLocal [↑x.N, ↑x.D, ↑x.w, ↑x.U, ↑x.x, ↑x.y, ↑x.wi, ↑x.wj, ↑x.out, ↑fr] 10 r) 10 j), wrote μ₁ x.out f j⟩ := by
      constructor
      · exact hOpSafe
      · have hv :
            (Light.Expr.op Light.Op.add (v 8) (v 10)).val
              ⟨Light.frame (Light.setLocal (Light.setLocal [↑x.N, ↑x.D, ↑x.w, ↑x.U, ↑x.x, ↑x.y, ↑x.wi, ↑x.wj, ↑x.out, ↑fr] 10 r) 10 j), wrote μ₁ x.out f j⟩ =
              (x.out + j : ℤ) := by
          simp [Light.Expr.val, Light.Op.eval, Light.frame, Light.setLocal]
        rw [hv]
        exact ⟨by positivity, by exact_mod_cast haddrNat⟩
    have hCondSafe :
        (Light.Cond.eq (M (Light.Expr.op Light.Op.add (v 8) (v 10))) (k 0)).Safe lim
          ⟨Light.frame (Light.setLocal (Light.setLocal [↑x.N, ↑x.D, ↑x.w, ↑x.U, ↑x.x, ↑x.y, ↑x.wi, ↑x.wj, ↑x.out, ↑fr] 10 r) 10 j), wrote μ₁ x.out f j⟩ := by
      constructor
      · exact hLoadSafe
      · change (0 : ℤ) ≤ lim.word
        exact le_trans (Int.natCast_nonneg _) hok.space
    have hidx : (↑x.out + ↑j : ℤ).toNat = x.out + j := by rfl
    have hstoreSafe :
        (Light.Expr.op Light.Op.add (v 8) (v 10)).Gives lim
          ⟨Light.frame (Light.setLocal (Light.setLocal [↑x.N, ↑x.D, ↑x.w, ↑x.U, ↑x.x, ↑x.y, ↑x.wi, ↑x.wj, ↑x.out, ↑fr] 10 r) 10 j), wrote μ₁ x.out f j⟩ (x.out + j) ∧
        (k 1).Gives lim
          ⟨Light.frame (Light.setLocal (Light.setLocal [↑x.N, ↑x.D, ↑x.w, ↑x.U, ↑x.x, ↑x.y, ↑x.wi, ↑x.wj, ↑x.out, ↑fr] 10 r) 10 j), wrote μ₁ x.out f j⟩ 1 ∧
        x.out + j < lim.space := by
      constructor
      · constructor
        · exact hOpSafe
        · rfl
      · constructor
        · constructor
          · change (1 : ℤ) ≤ lim.word
            exact hwordOne
          · rfl
        · exact haddrNat
    rw [← wrote_succ]
    refine Ends.iteLast (fun hc => Ends.skip ⟨rfl, ?_⟩)
      (fun hc => Ends.storeTo (x.out + j) 1 ⟨rfl, ?_⟩ (he := hstoreSafe)
        (hT := by simp [Light.Stmt.blockCost, Light.Expr.cost]))
      (hs := hCondSafe)
    · have hc' : μ₁ (x.out + j) = 0 := by
        change wrote μ₁ x.out f j ((↑x.out + ↑j : ℤ).toNat) = 0 at hc
        rw [hidx, hread] at hc
        exact hc
      have e : f j = wrote μ₁ x.out f j (x.out + j) := by rw [hf, if_pos hc', hread, hc']
      rw [e, Function.update_eq_self]
    · have hc' : μ₁ (x.out + j) ≠ 0 := by
        change ¬wrote μ₁ x.out f j ((↑x.out + ↑j : ℤ).toNat) = 0 at hc
        rw [hidx, hread] at hc
        exact hc
      rw [hf, if_neg hc']
  ·
    rintro _ rfl
    refine ⟨fun i hi => ?_, fun a ha => ?_⟩
    ·
      have hi' : i < x.w := by simpa [hlen] using hi
      rw [List.getElem_map, ← hseg i (by omega), ← hf]
      change wrote μ₁ x.out f x.w (x.out + i) = f i
      exact wrote_done hi'
    ·
      change wrote μ₁ x.out f x.w a = μ a
      calc
        wrote μ₁ x.out f x.w a = μ₁ a := wrote_rest ha.2
        _ = μ a := hk a ha
  ·
    constructor
    · intro e he
      have he' : e = v 0 ∨ e = v 1 ∨ e = v 2 ∨ e = v 3 ∨ e = v 4 ∨
          e = v 5 ∨ e = v 6 ∨ e = v 7 ∨ e = v 8 ∨ e = v 9 := by
        simpa using he
      rcases he' with h | h | h | h | h | h | h | h | h | h <;> subst e <;>
        simp [Light.Expr.Safe]
    · simp [Light.frame, Light.Expr.val]
  · omega
  · simp [Light.Expr.cost, Light.Stmt.blockCost, Light.Cond.cost] <;> omega

theorem rational_polyNeedN_detect {need : List ℕ → Need} (h : PolyNeedN need) :
    PolyNeedN (lopDetectNeed need) := by
  obtain ⟨s, e, h⟩ := h
  refine ⟨1 + s, e, fun ps => ?_⟩
  have h1 := Light.polyBound_le_succ s e ps
  obtain ⟨a, b, c⟩ := h ps
  simp only [lopDetectNeed]
  omega

end LopHosts

/-- The generic Corollary 15 conversion used below. -/
theorem rational_claim_lopDetectFromCount : Claim.LopDetectFromCount lightModel := by
  refine ⟨20, fun T hT => ?_⟩
  obtain ⟨P, p, Tn, need, hneed, hsol, htime⟩ := hT
  refine ⟨P ++ [lopDetectBody p], P.length, lopDetectTime Tn, lopDetectNeed need,
    LopHosts.rational_polyNeedN_detect hneed, ?_, fun n D w w' hn hD hw => ?_⟩
  · refine ⟨lopDetectBody p, by simp, fun R lim d x μ fr hpre hok => ?_⟩
    rw [List.append_assoc]
    exact LopHosts.rational_lop_detect_spec hsol hpre hok
  · have h1 := htime n D w w' hn hD hw
    have h2 : (w : ℝ) ≤ w' := by exact_mod_cast hw
    simp only [lopDetectTime, List.getD_cons_succ, List.getD_cons_zero]
    push_cast
    linarith

end Light.Sec3

namespace ThreeSumSharpTail

theorem detection_cost_from_native_count
    (G : Light.Sec4.RatParams) (a s : ℚ) (ha0 : 0 < a)
    (A B k : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hcost : ∀ N D : ℕ, 1 ≤ D → (D : ℝ) ≤ (N : ℝ) ^ (a : ℝ) →
      Light.Sec4.CostsWithinP G C N D
        ((N : ℝ) ^ 2 * (Real.log D + 1) ^ 2 / (D : ℝ) ^ (s : ℝ))
        ((D : ℝ) ^ (1 / 2 - (s : ℝ)) * (Real.log D + 1)))
    (heq : ∀ N D : ℕ, 1 ≤ N → 1 ≤ D →
      ((D : ℝ) ≤ (N : ℝ) ^ (a : ℝ) ↔ D ^ B ≤ N ^ A))
    (P : Light.Program) (p : ℕ) (Tn : List ℕ → ℕ) (need : List ℕ → Light.Need)
    (hneed : Light.PolyNeedN need) (hsol : Light.SolvesN Light.lopCountTask P p Tn need)
    (htime : ∀ N D w : ℕ, Tn [N, D, w] = k +
      if D ^ B ≤ N ^ A then Light.Sec4.tOffline32P Light.Sec4.cShared30 G N D w
      else 40 * ((w + 1) * (D + 1)))
    (hdetect : ThreeSumApsp.Claim.LopDetectFromCount Light.lightModel) :
    ∃ (K : ℝ) (Td : ℕ → ℕ → ℕ → ℝ), 0 ≤ K ∧ Light.lightModel.lopDetect Td ∧
      ∀ N D w : ℕ, 1 ≤ D → (D : ℝ) ≤ (N : ℝ) ^ (a : ℝ) →
        Td N D w ≤ K * ((N : ℝ) ^ 2 * (Real.log D + 1) ^ 2 / (D : ℝ) ^ (s : ℝ) +
          (w : ℝ) * (D : ℝ) ^ (1 / 2 - (s : ℝ)) * (Real.log D + 1) +
          (N : ℝ) * D + w + 1) := by
  let pre (N D : ℕ) : ℝ := (N : ℝ) ^ 2 * (Real.log D + 1) ^ 2 / (D : ℝ) ^ (s : ℝ)
  let query (D : ℕ) : ℝ := (D : ℝ) ^ (1 / 2 - (s : ℝ)) * (Real.log D + 1)
  have hpre0 (N D : ℕ) : 0 ≤ pre N D := by dsimp [pre]; positivity
  have hquery0 (D : ℕ) (hD : 1 ≤ D) : 0 ≤ query D := by
    dsimp [query]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ D by exact_mod_cast hD)])
  obtain ⟨L, hL⟩ := ThreeSumSharpTail.pruned_offline_steps G C hC Light.Sec4.cShared30 k
  let c : ℝ := max 0 L
  have hc : 0 ≤ c := le_max_left _ _
  let Tc (N D w : ℕ) : ℝ := if D ^ B ≤ N ^ A then c * (pre N D + (w : ℝ) * query D)
    else (k : ℝ) + 40 * (((w : ℝ) + 1) * ((D : ℝ) + 1))
  have hcount : Light.lightModel.lopCount Tc := by
    refine ⟨P, p, Tn, need, hneed, hsol, fun N D w w' hN hD hww => ?_⟩
    rw [htime N D w]
    dsimp [Tc]
    by_cases hr : D ^ B ≤ N ^ A
    · rw [if_pos hr, if_pos hr]
      have hh := hL N D (pre N D) (query D) w (hcost N D hD ((heq N D hN hD).mpr hr))
      have hbase : 0 ≤ pre N D + (w : ℝ) * query D :=
        add_nonneg (hpre0 N D) (mul_nonneg (by positivity) (hquery0 D hD))
      have hwwR : (w : ℝ) ≤ (w' : ℝ) := by exact_mod_cast hww
      have hmono : pre N D + (w : ℝ) * query D ≤ pre N D + (w' : ℝ) * query D := by
        simpa only [add_comm] using
          add_le_add_left (mul_le_mul_of_nonneg_right hwwR (hquery0 D hD)) (pre N D)
      have hh0 : (k : ℝ) + (Light.Sec4.tOffline32P Light.Sec4.cShared30 G N D w : ℝ) ≤
          L * (pre N D + (w : ℝ) * query D) := by simpa only [add_comm] using hh
      have hh' : (k : ℝ) + (Light.Sec4.tOffline32P Light.Sec4.cShared30 G N D w : ℝ) ≤
          c * (pre N D + (w' : ℝ) * query D) :=
        hh0.trans
          ((mul_le_mul_of_nonneg_right (le_max_right 0 L) hbase).trans
            (mul_le_mul_of_nonneg_left hmono hc))
      simpa only [Nat.cast_add] using hh'
    · rw [if_neg hr, if_neg hr]
      push_cast
      gcongr
  obtain ⟨J, hJ⟩ := hdetect
  refine ⟨c + max 0 J, fun N D w => Tc N D w + J * ((w : ℝ) + 1),
    add_nonneg hc (le_max_left _ _), hJ Tc hcount, fun N D w hD hr => ?_⟩
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha0
  have hN : 1 ≤ N := by
    by_contra hN
    have hN0 : N = 0 := by omega
    have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
    simp only [hN0, Nat.cast_zero, Real.zero_rpow (ne_of_gt haR)] at hr
    linarith
  have hnat : D ^ B ≤ N ^ A := (heq N D hN hD).mp hr
  change Tc N D w + J * ((w : ℝ) + 1) ≤ _
  dsimp [Tc]
  rw [if_pos hnat]
  have hb0 : 0 ≤ pre N D + (w : ℝ) * query D :=
    add_nonneg (hpre0 N D) (mul_nonneg (by positivity) (hquery0 D hD))
  have ho0 : 0 ≤ (N : ℝ) * D + w + 1 := by positivity
  have hw1 : (w : ℝ) + 1 ≤ (N : ℝ) * D + w + 1 := by
    nlinarith [mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (Nat.cast_nonneg D : (0 : ℝ) ≤ D)]
  have hj0 : 0 ≤ max 0 J := le_max_left _ _
  have hover : J * ((w : ℝ) + 1) ≤ max 0 J * ((N : ℝ) * D + w + 1) :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hw1 hj0)
  have hfinal : c * (pre N D + (w : ℝ) * query D) + J * ((w : ℝ) + 1) ≤
      (c + max 0 J) * (pre N D + (w : ℝ) * query D + (N : ℝ) * D + w + 1) := by
    nlinarith [mul_nonneg hc ho0, mul_nonneg hj0 hb0]
  simpa only [pre, query, mul_assoc] using hfinal

end ThreeSumSharpTail

open ThreeSumSharpTail in
theorem solution
    (G : Light.Sec4.RatParams) (a s : ℚ)
    (ha0 : 0 < a) (ha1 : a < 1) (hs0 : 0 < s) (hsHalf : s < 1 / 2)
    (hcost : ∃ C : ℝ, 0 ≤ C ∧ ∀ N D : ℕ,
      1 ≤ D → (D : ℝ) ≤ (N : ℝ) ^ (a : ℝ) →
      Light.Sec4.CostsWithinP G C N D
        ((N : ℝ) ^ 2 * (Real.log D + 1) ^ 2 / (D : ℝ) ^ (s : ℝ))
        ((D : ℝ) ^ (1 / 2 - (s : ℝ)) * (Real.log D + 1))) :
    ∃ (C : ℝ) (Td : ℕ → ℕ → ℕ → ℝ), 0 ≤ C ∧ Light.lightModel.lopDetect Td ∧
      ∀ n d w : ℕ, 1 ≤ d → (d : ℝ) ≤ (n : ℝ) ^ (a : ℝ) →
        Td n d w ≤ C * ((n : ℝ) ^ 2 * (Real.log d + 1) ^ 2 / (d : ℝ) ^ (s : ℝ) +
          (w : ℝ) * (d : ℝ) ^ (1 / 2 - (s : ℝ)) * (Real.log d + 1) + (n : ℝ) * d + w + 1) := by
  obtain ⟨A, B, _c, _e, hB, he, hAB, hce, haEq, _hsEq, heq⟩ :=
    ThreeSumSharpTail.rational_power_representation a s ha0 ha1 hs0 hsHalf
  obtain ⟨C, hC, hcost⟩ := hcost
  obtain ⟨baseNeed, hbaseNeed, hbaseCount⟩ :=
    rationalRegime_count_solves G a s A B C hC hcost heq
  let need := rationalRegimeCountNeed A B baseNeed
  have hneed : Light.PolyNeedN need := by
    simpa [need] using rationalRegimeCountNeed_poly A B hbaseNeed
  have hcount : Light.SolvesN Light.lopCountTask (rationalRegimeProgram G A B)
      (rationalRegimeWrapperIndex G) (rationalRegimeCountTime G A B) need := by
    simpa [need] using hbaseCount
  have htime : ∀ N D w : ℕ,
      rationalRegimeCountTime G A B [N, D, w] =
        (regimeTestSteps A B + 20) +
          if D ^ B ≤ N ^ A then Light.Sec4.tOffline32P Light.Sec4.cShared30 G N D w
          else 40 * ((w + 1) * (D + 1)) := by
    intro N D w
    simp [rationalRegimeCountTime]
  exact detection_cost_from_native_count G a s ha0 A B (regimeTestSteps A B + 20)
    C hC hcost heq (rationalRegimeProgram G A B) (rationalRegimeWrapperIndex G)
    (rationalRegimeCountTime G A B) need hneed hcount htime
    Light.Sec3.rational_claim_lopDetectFromCount

#print axioms solution

