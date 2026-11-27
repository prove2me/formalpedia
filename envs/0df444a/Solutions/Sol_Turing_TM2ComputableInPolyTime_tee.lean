-- Prove2me | solution 1 for Turing.TM2ComputableInPolyTime.tee
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:24:21.980977+00:00
-- url     : https://prove2.me/submissions/a6f3b52d-7e68-4c9b-9a2e-13c0a333ded7

import Mathlib


set_option autoImplicit false

open Turing StateTransition

/-! ### Growth and size bounds (from the swarm's `Growth.lean`) -/

attribute [instance] Turing.FinTM2.kDecidableEq Turing.FinTM2.kFin Turing.FinTM2.ΛFin
  Turing.FinTM2.σFin Turing.FinTM2.Γk₀Fin

namespace Turing

namespace TM2

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

/-- The number of `push` statements executed inside a single statement chain.

A single `TM2.step` runs a whole chain (`push`/`peek`/`pop`/`load`/`branch` continue within the
same step), ending at `goto` or `halt`; `pushes` therefore bounds the number of symbols that a step
can add to the stacks. -/
def pushes : Stmt Γ Λ σ → ℕ
  | .push _ _ q => 1 + pushes q
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q r => max (pushes q) (pushes r)
  | .goto _ => 0
  | .halt => 0

variable [Fintype K] [DecidableEq K]

/-- Total number of symbols stored on all stacks. -/
def volume (s : (k : K) → List (Γ k)) : ℕ := ∑ k, (s k).length

theorem length_update (s : (k : K) → List (Γ k)) (k : K) (v : List (Γ k)) :
    (fun j => (Function.update s k v j).length) =
      Function.update (fun j => (s j).length) k v.length := by
  funext j
  by_cases h : j = k
  · subst h
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h, Function.update_of_ne h]

theorem volume_update (s : (k : K) → List (Γ k)) (k : K) (v : List (Γ k)) :
    volume (Function.update s k v) + (s k).length = volume s + v.length := by
  classical
  unfold volume
  rw [length_update, Finset.sum_update_of_mem (Finset.mem_univ k)]
  have hh := Finset.sum_erase_add (Finset.univ : Finset K) (fun j => (s j).length)
    (Finset.mem_univ k)
  rw [Finset.sdiff_singleton_eq_erase]
  omega

theorem stepAux_volume (q : Stmt Γ Λ σ) (v : σ) (s : (k : K) → List (Γ k)) :
    volume (TM2.stepAux q v s).stk ≤ volume s + pushes q := by
  induction q generalizing v s with
  | push k g q ih =>
      have hv := volume_update s k (g v :: s k)
      simp only [List.length_cons] at hv
      have hq := ih v (Function.update s k (g v :: s k))
      simp only [TM2.stepAux, pushes]
      omega
  | peek k g q ih => exact ih _ _
  | pop k g q ih =>
      have hv := volume_update s k (s k).tail
      have hl := List.length_tail (l := s k)
      have hq := ih (g v (s k).head?) (Function.update s k (s k).tail)
      simp only [TM2.stepAux, pushes]
      omega
  | load g q ih => exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v
      · simp only [TM2.stepAux, hg, Bool.cond_false, pushes]
        exact (ihr v s).trans (Nat.add_le_add_left (le_max_right (pushes q) _) _)
      · simp only [TM2.stepAux, hg, Bool.cond_true, pushes]
        exact (ihq v s).trans (Nat.add_le_add_left (le_max_left _ (pushes r)) _)
  | goto g => simp only [TM2.stepAux, pushes, Nat.add_zero]; exact le_refl _
  | halt => simp only [TM2.stepAux, pushes, Nat.add_zero]; exact le_refl _

end TM2

open TM2 in
/-- Number of symbols a machine can add to all of its stacks in one step, summed over its program. -/
noncomputable def FinTM2.growth (tm : FinTM2) : ℕ := ∑ l, TM2.pushes (tm.m l)

namespace FinTM2

variable (tm : FinTM2)

theorem flip_bind_none : (flip bind tm.step) (none : Option tm.Cfg) = none := rfl

theorem flip_bind_some (c : tm.Cfg) : (flip bind tm.step) (some c) = tm.step c := rfl

theorem step_volume {a b : tm.Cfg} (h : tm.step a = some b) :
    TM2.volume b.stk ≤ TM2.volume a.stk + tm.growth := by
  classical
  obtain ⟨l, v, s⟩ := a
  cases l with
  | none => exact absurd h (by simp [FinTM2.step, TM2.step])
  | some l =>
      have hb : b = TM2.stepAux (tm.m l) v s := (Option.some.inj h).symm
      rw [hb, FinTM2.growth]
      refine (TM2.stepAux_volume _ _ _).trans (Nat.add_le_add_left ?_ _)
      exact Finset.single_le_sum (f := fun x => TM2.pushes (tm.m x))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)

theorem iterate_volume (tm : FinTM2) : ∀ (m : ℕ) (a b : tm.Cfg),
    (flip bind tm.step)^[m] (some a) = some b →
      TM2.volume b.stk ≤ TM2.volume a.stk + m * tm.growth
  | 0, a, b, h => by
      simp only [Function.iterate_zero, id_eq, Option.some.injEq] at h
      subst h; simp
  | m + 1, a, b, h => by
      rw [Function.iterate_succ_apply'] at h
      cases hprev : (flip bind tm.step)^[m] (some a) with
      | none => rw [hprev, tm.flip_bind_none] at h; exact absurd h (by simp)
      | some c =>
          rw [hprev, tm.flip_bind_some] at h
          have ih := iterate_volume tm m a c hprev
          have hs := tm.step_volume h
          have hmul : (m + 1) * tm.growth = m * tm.growth + tm.growth := Nat.succ_mul _ _
          rw [hmul]
          omega

theorem volume_initList (s : List (tm.Γ tm.k₀)) : TM2.volume (initList tm s).stk = s.length := by
  classical
  unfold TM2.volume
  rw [Finset.sum_eq_single tm.k₀]
  · simp [initList]
  · intro k _ hk
    simp only [initList, dif_neg hk, List.length_nil]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem volume_haltList (s : List (tm.Γ tm.k₁)) : TM2.volume (haltList tm s).stk = s.length := by
  classical
  unfold TM2.volume
  rw [Finset.sum_eq_single tm.k₁]
  · simp [haltList]
  · intro k _ hk
    simp only [haltList, dif_neg hk, List.length_nil]
  · intro h; exact absurd (Finset.mem_univ _) h

end FinTM2

end Turing

namespace StateTransition

variable {α : Type*}

/-- A step bound may always be weakened. -/
def EvalsToInTime.mono {f : α → Option α} {a : α} {b : Option α} {m m' : ℕ}
    (h : EvalsToInTime f a b m) (hm : m ≤ m') : EvalsToInTime f a b m' :=
  ⟨h.toEvalsTo, le_trans h.steps_le_m hm⟩

end StateTransition

namespace Turing

/-- **Output length bound for an arbitrary `FinTM2`.** If `tm` outputs `t` on input `s` within `n`
steps, then `t` has at most `s.length + n * growth` symbols. -/
theorem TM2OutputsInTime.output_length_le {tm : FinTM2} {s : List (tm.Γ tm.k₀)}
    {t : List (tm.Γ tm.k₁)} {n : ℕ}
    (h : TM2OutputsInTime tm s (some t) n) : t.length ≤ s.length + n * tm.growth := by
  have hvol := tm.iterate_volume h.steps (initList tm s) (haltList tm t) h.evals_in_steps
  rw [tm.volume_initList, tm.volume_haltList] at hvol
  exact hvol.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ h.steps_le_m) _)

end Turing


set_option autoImplicit false

open Turing StateTransition

namespace TeeCore

/-! ### Generic stack-moving loops -/

section Generic

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

def ev_trans {α : Type} {f : α → Option α} {a b : α} {c : Option α} {m₁ m₂ : ℕ}
    (h₁ : EvalsToInTime f a (some b) m₁) (h₂ : EvalsToInTime f b c m₂) :
    EvalsToInTime f a c (m₂ + m₁) :=
  EvalsToInTime.trans f m₁ m₂ a b c h₁ h₂

def ev_mono {α : Type} {f : α → Option α} {a : α} {b : Option α} {m m' : ℕ}
    (h : EvalsToInTime f a b m) (hm : m ≤ m') : EvalsToInTime f a b m' :=
  ⟨h.toEvalsTo, le_trans h.steps_le_m hm⟩

def ev_congr {α : Type} {f : α → Option α} {a a' : α} {b b' : Option α} {m : ℕ}
    (ha : a = a') (hb : b = b') (h : EvalsToInTime f a b m) : EvalsToInTime f a' b' m := by
  subst ha; subst hb; exact h

def ev_one {α : Type} {f : α → Option α} {a b : α} (h : f a = some b) :
    EvalsToInTime f a (some b) 1 :=
  ⟨⟨1, by rw [Function.iterate_one]; exact h⟩, le_rfl⟩

/-- Move the contents of `src` onto `dst` (reversing), one symbol per step. -/
def mv (src dst : K) (g : Γ src → Bool) (h : Bool → Γ dst) (self next : Λ) :
    TM2.Stmt Γ Λ (σ × Option Bool) :=
  .pop src (fun v o => (v.1, o.map g))
    (.branch (fun v => v.2.isSome)
      (.push dst (fun v => h (v.2.getD false)) (.goto fun _ => self))
      (.goto fun _ => next))

/-- Move the contents of `src` onto both `d₁` and `d₂`. -/
def mv2 (src d₁ d₂ : K) (g : Γ src → Bool) (h₁ : Bool → Γ d₁) (h₂ : Bool → Γ d₂)
    (self next : Λ) : TM2.Stmt Γ Λ (σ × Option Bool) :=
  .pop src (fun v o => (v.1, o.map g))
    (.branch (fun v => v.2.isSome)
      (.push d₁ (fun v => h₁ (v.2.getD false))
        (.push d₂ (fun v => h₂ (v.2.getD false)) (.goto fun _ => self)))
      (.goto fun _ => next))

theorem upd_upd_ne (S : (k : K) → List (Γ k)) {a b : K} (hab : a ≠ b)
    (x : List (Γ a)) : (Function.update S a x) b = S b :=
  Function.update_of_ne (Ne.symm hab) _ _

def mv_run {M : Λ → TM2.Stmt Γ Λ (σ × Option Bool)} {src dst : K} {g : Γ src → Bool}
    {h : Bool → Γ dst} {self next : Λ} (hM : M self = mv src dst g h self next)
    (hne : src ≠ dst) :
    ∀ (L : List (Γ src)) (v : σ × Option Bool) (S : (k : K) → List (Γ k)), S src = L →
      EvalsToInTime (TM2.step M) ⟨some self, v, S⟩
        (some ⟨some next, (v.1, none), Function.update (Function.update S src []) dst
          ((L.map (fun x => h (g x))).reverse ++ S dst)⟩) (L.length + 1)
  | [], v, S, hS => by
      have hstep : TM2.step M ⟨some self, v, S⟩ =
          some ⟨some next, (v.1, none), Function.update S src []⟩ := by
        show some (TM2.stepAux (M self) v S) = _
        rw [hM]
        simp [mv, TM2.stepAux, hS]
      refine ev_congr rfl ?_ (ev_one hstep)
      have e : Function.update (Function.update S src []) dst
          ((([] : List (Γ src)).map (fun x => h (g x))).reverse ++ S dst) = Function.update S src [] := by
        simp only [List.map_nil, List.reverse_nil, List.nil_append]
        rw [← upd_upd_ne S hne ([] : List (Γ src)), Function.update_eq_self]
      rw [e]
  | x :: xs, v, S, hS => by
      have hstep : TM2.step M ⟨some self, v, S⟩ =
          some ⟨some self, (v.1, some (g x)),
            Function.update (Function.update S src xs) dst (h (g x) :: S dst)⟩ := by
        show some (TM2.stepAux (M self) v S) = _
        rw [hM]
        simp [mv, TM2.stepAux, hS, upd_upd_ne S hne]
      have hS' : (Function.update (Function.update S src xs) dst (h (g x) :: S dst)) src = xs := by
        rw [Function.update_of_ne hne, Function.update_self]
      have ih := mv_run hM hne xs (v.1, some (g x)) _ hS'
      refine ev_mono (ev_congr rfl ?_ (ev_trans (ev_one hstep) ih))
        (by simp only [List.length_cons]; omega)
      have e : Function.update (Function.update (Function.update (Function.update S src xs) dst
            (h (g x) :: S dst)) src []) dst ((xs.map (fun x => h (g x))).reverse ++
            Function.update (Function.update S src xs) dst (h (g x) :: S dst) dst)
          = Function.update (Function.update S src []) dst
            (((x :: xs).map (fun x => h (g x))).reverse ++ S dst) := by
        rw [Function.update_self, Function.update_comm (Ne.symm hne) _ _ (Function.update S src xs),
          Function.update_idem, Function.update_idem]
        simp
      rw [e]

def mv2_run {M : Λ → TM2.Stmt Γ Λ (σ × Option Bool)} {src d₁ d₂ : K} {g : Γ src → Bool}
    {h₁ : Bool → Γ d₁} {h₂ : Bool → Γ d₂} {self next : Λ}
    (hM : M self = mv2 src d₁ d₂ g h₁ h₂ self next)
    (hn1 : src ≠ d₁) (hn2 : src ≠ d₂) (h12 : d₁ ≠ d₂) :
    ∀ (L : List (Γ src)) (v : σ × Option Bool) (S : (k : K) → List (Γ k)), S src = L →
      EvalsToInTime (TM2.step M) ⟨some self, v, S⟩
        (some ⟨some next, (v.1, none), Function.update (Function.update
          (Function.update S src []) d₁ ((L.map (fun x => h₁ (g x))).reverse ++ S d₁)) d₂
          ((L.map (fun x => h₂ (g x))).reverse ++ S d₂)⟩) (L.length + 1)
  | [], v, S, hS => by
      have hstep : TM2.step M ⟨some self, v, S⟩ =
          some ⟨some next, (v.1, none), Function.update S src []⟩ := by
        show some (TM2.stepAux (M self) v S) = _
        rw [hM]
        simp [mv2, TM2.stepAux, hS]
      refine ev_congr rfl ?_ (ev_one hstep)
      have e : Function.update (Function.update
          (Function.update S src []) d₁ ((([] : List (Γ src)).map (fun x => h₁ (g x))).reverse ++ S d₁)) d₂
          ((([] : List (Γ src)).map (fun x => h₂ (g x))).reverse ++ S d₂) = Function.update S src [] := by
        simp only [List.map_nil, List.reverse_nil, List.nil_append]
        rw [← upd_upd_ne S hn1 ([] : List (Γ src)), Function.update_eq_self,
          ← upd_upd_ne S hn2 ([] : List (Γ src)), Function.update_eq_self]
      rw [e]
  | x :: xs, v, S, hS => by
      have hstep : TM2.step M ⟨some self, v, S⟩ =
          some ⟨some self, (v.1, some (g x)),
            Function.update (Function.update (Function.update S src xs) d₁ (h₁ (g x) :: S d₁))
              d₂ (h₂ (g x) :: S d₂)⟩ := by
        show some (TM2.stepAux (M self) v S) = _
        rw [hM]
        simp [mv2, TM2.stepAux, hS, upd_upd_ne S hn1, upd_upd_ne S hn2,
          upd_upd_ne _ h12]
      have hS' : (Function.update (Function.update (Function.update S src xs) d₁
          (h₁ (g x) :: S d₁)) d₂ (h₂ (g x) :: S d₂)) src = xs := by
        rw [Function.update_of_ne hn2, Function.update_of_ne hn1, Function.update_self]
      have ih := mv2_run hM hn1 hn2 h12 xs (v.1, some (g x)) _ hS'
      refine ev_mono (ev_congr rfl ?_ (ev_trans (ev_one hstep) ih))
        (by simp only [List.length_cons]; omega)
      have e : Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update S src xs) d₁ (h₁ (g x) :: S d₁)) d₂ (h₂ (g x) :: S d₂))
            src []) d₁ ((xs.map (fun x => h₁ (g x))).reverse ++ Function.update (Function.update
            (Function.update S src xs) d₁ (h₁ (g x) :: S d₁)) d₂ (h₂ (g x) :: S d₂) d₁)) d₂
            ((xs.map (fun x => h₂ (g x))).reverse ++ Function.update (Function.update
            (Function.update S src xs) d₁ (h₁ (g x) :: S d₁)) d₂ (h₂ (g x) :: S d₂) d₂)
          = Function.update (Function.update (Function.update S src []) d₁
            (((x :: xs).map (fun x => h₁ (g x))).reverse ++ S d₁)) d₂
            (((x :: xs).map (fun x => h₂ (g x))).reverse ++ S d₂) := by
        rw [Function.update_self, Function.update_of_ne h12, Function.update_self,
          Function.update_comm (Ne.symm hn2) _ _ (Function.update (Function.update S src xs) d₁ _),
          Function.update_comm (Ne.symm hn1) _ _ (Function.update S src xs),
          Function.update_idem,
          Function.update_comm (Ne.symm h12) _ _ (Function.update (Function.update S src []) d₁ _),
          Function.update_idem, Function.update_idem]
        simp
      rw [e]

end Generic

end TeeCore


set_option autoImplicit false

open Turing StateTransition

namespace TeeCore

variable (tm : FinTM2)

abbrev Key : Type := tm.K ⊕ Fin 4

abbrev Gam : Key tm → Type
  | .inl a => tm.Γ a
  | .inr _ => Bool

abbrev Lab : Type := tm.Λ ⊕ Fin 6

abbrev Sta : Type := tm.σ × Option Bool

def pack (S : (k : tm.K) → List (tm.Γ k)) (E : Fin 4 → List Bool) :
    (k : Key tm) → List (Gam tm k)
  | .inl a => S a
  | .inr i => E i

theorem pack_update_inl (S : (k : tm.K) → List (tm.Γ k)) (E : Fin 4 → List Bool)
    (k : tm.K) (x : List (tm.Γ k)) :
    Function.update (pack tm S E) (Sum.inl k) x = pack tm (Function.update S k x) E := by
  funext j
  rcases j with a | i
  · by_cases h : a = k
    · subst h; simp [pack]
    · rw [Function.update_of_ne (by simpa using h)]
      simp [pack, Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]
    rfl

theorem pack_update_inr (S : (k : tm.K) → List (tm.Γ k)) (E : Fin 4 → List Bool)
    (i : Fin 4) (x : List Bool) :
    Function.update (pack tm S E) (Sum.inr i) x = pack tm S (Function.update E i x) := by
  funext j
  rcases j with a | i'
  · rw [Function.update_of_ne (by simp)]
    rfl
  · by_cases h : i' = i
    · subst h; simp [pack]
    · rw [Function.update_of_ne (by simpa using h)]
      simp [pack, Function.update_of_ne h]

@[simp] theorem pack_inl (S : (k : tm.K) → List (tm.Γ k)) (E : Fin 4 → List Bool) (k : tm.K) :
    pack tm S E (Sum.inl k) = S k := rfl

@[simp] theorem pack_inr (S : (k : tm.K) → List (tm.Γ k)) (E : Fin 4 → List Bool) (i : Fin 4) :
    pack tm S E (Sum.inr i) = E i := rfl

def labT : Option tm.Λ → Option (Lab tm)
  | none => some (Sum.inr 2)
  | some l => some (Sum.inl l)

def tr : TM2.Stmt tm.Γ tm.Λ tm.σ → TM2.Stmt (Gam tm) (Lab tm) (Sta tm)
  | .push k g q => .push (Sum.inl k) (fun s => g s.1) (tr q)
  | .peek k g q => .peek (Sum.inl k) (fun s o => (g s.1 o, s.2)) (tr q)
  | .pop k g q => .pop (Sum.inl k) (fun s o => (g s.1 o, s.2)) (tr q)
  | .load g q => .load (fun s => (g s.1, s.2)) (tr q)
  | .branch g q r => .branch (fun s => g s.1) (tr q) (tr r)
  | .goto g => .goto (fun s => Sum.inl (g s.1))
  | .halt => .goto (fun _ => Sum.inr 2)

theorem stepAux_tr (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (v : tm.σ) (b : Option Bool)
    (S : (k : tm.K) → List (tm.Γ k)) (E : Fin 4 → List Bool) :
    TM2.stepAux (tr tm q) (v, b) (pack tm S E)
      = ⟨labT tm (TM2.stepAux q v S).l, ((TM2.stepAux q v S).var, b),
          pack tm (TM2.stepAux q v S).stk E⟩ := by
  induction q generalizing v S with
  | push k g q ih =>
      simp only [tr, TM2.stepAux, pack_update_inl]
      exact ih _ _
  | peek k g q ih =>
      simp only [tr, TM2.stepAux]
      exact ih _ _
  | pop k g q ih =>
      simp only [tr, TM2.stepAux, pack_update_inl]
      exact ih _ _
  | load g q ih =>
      simp only [tr, TM2.stepAux]
      exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v
      · simp only [tr, TM2.stepAux, hg, Bool.cond_false]
        exact ihr _ _
      · simp only [tr, TM2.stepAux, hg, Bool.cond_true]
        exact ihq _ _
  | goto g => simp only [tr, TM2.stepAux, labT]
  | halt => simp only [tr, TM2.stepAux, labT]

variable {tm}

def prog (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) :
    Lab tm → TM2.Stmt (Gam tm) (Lab tm) (Sta tm)
  | .inl l => tr tm (tm.m l)
  | .inr 0 => mv2 (Γ := Gam tm) (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) id id id (Sum.inr 0) (Sum.inr 1)
  | .inr 1 => mv (Γ := Gam tm) (Sum.inr 2) (Sum.inl tm.k₀) id ia.symm (Sum.inr 1) (Sum.inl tm.main)
  | .inr 2 => mv (Γ := Gam tm) (Sum.inl tm.k₁) (Sum.inr 2) oa id (Sum.inr 2) (Sum.inr 3)
  | .inr 3 => mv (Γ := Gam tm) (Sum.inr 2) (Sum.inr 3) id id (Sum.inr 3) (Sum.inr 4)
  | .inr 4 => mv (Γ := Gam tm) (Sum.inr 1) (Sum.inr 3) id id (Sum.inr 4) (Sum.inr 5)
  | .inr 5 => .halt

theorem step_tr (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) (b : Option Bool)
    (E : Fin 4 → List Bool) {c c' : TM2.Cfg tm.Γ tm.Λ tm.σ} (h : tm.step c = some c') :
    TM2.step (prog ia oa) ⟨labT tm c.l, (c.var, b), pack tm c.stk E⟩
      = some ⟨labT tm c'.l, (c'.var, b), pack tm c'.stk E⟩ := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [FinTM2.step, TM2.step] at h
  | some l =>
      have hh : c' = TM2.stepAux (tm.m l) v S := (Option.some.inj h).symm
      subst hh
      show some (TM2.stepAux (tr tm (tm.m l)) (v, b) (pack tm S E)) = _
      rw [stepAux_tr]

theorem iterate_none' {α : Type} (f : α → Option α) : ∀ m : ℕ,
    (flip bind f)^[m] (none : Option α) = none
  | 0 => rfl
  | m + 1 => by
      rw [Function.iterate_succ_apply]
      exact iterate_none' f m

theorem iterate_tr (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) (b : Option Bool)
    (E : Fin 4 → List Bool) :
    ∀ (m : ℕ) (c c' : TM2.Cfg tm.Γ tm.Λ tm.σ),
      (flip bind tm.step)^[m] (some c) = some c' →
      (flip bind (TM2.step (prog ia oa)))^[m] (some ⟨labT tm c.l, (c.var, b), pack tm c.stk E⟩)
        = some ⟨labT tm c'.l, (c'.var, b), pack tm c'.stk E⟩
  | 0, c, c', h => by
      simp only [Function.iterate_zero, id_eq] at h
      have h' : c = c' := Option.some.inj h
      subst h'; rfl
  | m + 1, c, c', h => by
      rw [Function.iterate_succ_apply] at h ⊢
      rw [show (flip bind tm.step) (some c) = tm.step c from rfl] at h
      cases hstep : tm.step c with
      | none => rw [hstep] at h; exact absurd h (by rw [iterate_none']; simp)
      | some d =>
          rw [hstep] at h
          rw [show (flip bind (TM2.step (prog ia oa))) (some ⟨labT tm c.l, (c.var, b), pack tm c.stk E⟩)
                = TM2.step (prog ia oa) ⟨labT tm c.l, (c.var, b), pack tm c.stk E⟩ from rfl,
              step_tr ia oa b E hstep]
          exact iterate_tr ia oa b E m d c' h

variable (tm)

/-- The tee machine. -/
noncomputable abbrev teeTM (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) : FinTM2 where
  K := Key tm
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := Sum.inr 0
  k₁ := Sum.inr 3
  Γ := Gam tm
  Λ := Lab tm
  main := Sum.inr 0
  ΛFin := inferInstance
  σ := Sta tm
  initialState := (tm.initialState, none)
  σFin := inferInstance
  Γk₀Fin := (inferInstance : Fintype Bool)
  m := prog ia oa

end TeeCore


set_option autoImplicit false

open Turing StateTransition

namespace TeeCore

variable {tm : FinTM2}

theorem initList_stk_eq (l : List (tm.Γ tm.k₀)) :
    (initList tm l).stk = Function.update (fun k => ([] : List (tm.Γ k))) tm.k₀ l := by
  funext k
  by_cases h : k = tm.k₀
  · subst h; simp [initList]
  · simp [initList, h]

theorem haltList_stk_eq (l : List (tm.Γ tm.k₁)) :
    (haltList tm l).stk = Function.update (fun k => ([] : List (tm.Γ k))) tm.k₁ l := by
  funext k
  by_cases h : k = tm.k₁
  · subst h; simp [haltList]
  · simp [haltList, h]

theorem vec_ext {a b c d a' b' c' d' : List Bool} (h1 : a = a') (h2 : b = b') (h3 : c = c')
    (h4 : d = d') : (![a, b, c, d] : Fin 4 → List Bool) = ![a', b', c', d'] := by
  subst h1 h2 h3 h4; rfl

theorem upd_vec0 (a b c d x : List Bool) :
    Function.update (![a, b, c, d] : Fin 4 → List Bool) 0 x = ![x, b, c, d] := by
  funext i; fin_cases i <;> rfl
theorem upd_vec1 (a b c d x : List Bool) :
    Function.update (![a, b, c, d] : Fin 4 → List Bool) 1 x = ![a, x, c, d] := by
  funext i; fin_cases i <;> rfl
theorem upd_vec2 (a b c d x : List Bool) :
    Function.update (![a, b, c, d] : Fin 4 → List Bool) 2 x = ![a, b, x, d] := by
  funext i; fin_cases i <;> rfl
theorem upd_vec3 (a b c d x : List Bool) :
    Function.update (![a, b, c, d] : Fin 4 → List Bool) 3 x = ![a, b, c, x] := by
  funext i; fin_cases i <;> rfl

@[simp] theorem vec_0 (a b c d : List Bool) : (![a, b, c, d] : Fin 4 → List Bool) 0 = a := rfl
@[simp] theorem vec_1 (a b c d : List Bool) : (![a, b, c, d] : Fin 4 → List Bool) 1 = b := rfl
@[simp] theorem vec_2 (a b c d : List Bool) : (![a, b, c, d] : Fin 4 → List Bool) 2 = c := rfl
@[simp] theorem vec_3 (a b c d : List Bool) : (![a, b, c, d] : Fin 4 → List Bool) 3 = d := rfl

/-- The whole run of the tee machine. -/
noncomputable def tee_run (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool)
    (w u : List Bool) (T : ℕ)
    (h : TM2OutputsInTime tm (w.map ia.symm) (some (u.map oa.symm)) T) :
    EvalsToInTime (TM2.step (prog ia oa))
      ⟨some (Sum.inr 0), (tm.initialState, none), pack tm (fun _ => []) ![w, [], [], []]⟩
      (some ⟨none, (tm.initialState, none), pack tm (fun _ => []) ![[], [], [], w ++ u]⟩)
      (1 + ((w.length + 1) + ((u.length + 1) + ((u.length + 1) + (T + ((w.length + 1) +
        (w.length + 1))))))) := by
  -- stage A
  have hA := mv2_run (M := prog ia oa) (src := (Sum.inr 0 : Key tm)) (d₁ := Sum.inr 1)
    (d₂ := Sum.inr 2) (g := id) (h₁ := id) (h₂ := id) (self := Sum.inr 0) (next := Sum.inr 1)
    rfl (by simp) (by simp) (by simp) w (tm.initialState, none)
    (pack tm (fun _ => []) ![w, [], [], []]) rfl
  simp only [pack_update_inr, pack_inr, upd_vec0, upd_vec1, upd_vec2, vec_1, vec_2,
    List.append_nil, id, List.map_id'] at hA
  -- stage B
  have hB := mv_run (M := prog ia oa) (src := (Sum.inr 2 : Key tm)) (dst := Sum.inl tm.k₀)
    (g := id) (h := ia.symm) (self := Sum.inr 1) (next := Sum.inl tm.main)
    rfl (by simp) w.reverse (tm.initialState, none)
    (pack tm (fun _ => []) ![[], w.reverse, w.reverse, []]) rfl
  simp only [pack_update_inr, pack_update_inl, pack_inr, pack_inl, upd_vec2, List.append_nil,
    id] at hB
  have hB' : EvalsToInTime (TM2.step (prog ia oa))
      ⟨some (Sum.inr 1), (tm.initialState, none), pack tm (fun _ => []) ![[], w.reverse, w.reverse, []]⟩
      (some ⟨labT tm (initList tm (w.map ia.symm)).l,
        ((initList tm (w.map ia.symm)).var, none),
        pack tm (initList tm (w.map ia.symm)).stk ![[], w.reverse, [], []]⟩) (w.length + 1) := by
    refine ev_congr rfl ?_ (ev_mono hB (by simp))
    rw [initList_stk_eq]
    simp [labT, initList, List.map_reverse]
  -- stage tm
  have hT : EvalsToInTime (TM2.step (prog ia oa))
      ⟨labT tm (initList tm (w.map ia.symm)).l, ((initList tm (w.map ia.symm)).var, none),
        pack tm (initList tm (w.map ia.symm)).stk ![[], w.reverse, [], []]⟩
      (some ⟨labT tm (haltList tm (u.map oa.symm)).l, ((haltList tm (u.map oa.symm)).var, none),
        pack tm (haltList tm (u.map oa.symm)).stk ![[], w.reverse, [], []]⟩) T :=
    ⟨⟨h.steps, iterate_tr ia oa none _ h.steps _ _ h.evals_in_steps⟩, h.steps_le_m⟩
  -- stage C
  have hC := mv_run (M := prog ia oa) (src := (Sum.inl tm.k₁ : Key tm)) (dst := Sum.inr 2)
    (g := oa) (h := id) (self := Sum.inr 2) (next := Sum.inr 3)
    rfl (by simp) (u.map oa.symm) (tm.initialState, none)
    (pack tm (haltList tm (u.map oa.symm)).stk ![[], w.reverse, [], []])
    (by rw [haltList_stk_eq]; simp)
  simp only [pack_update_inr, pack_update_inl, pack_inr, upd_vec2, List.append_nil,
    id, List.map_map] at hC
  have hC' : EvalsToInTime (TM2.step (prog ia oa))
      ⟨labT tm (haltList tm (u.map oa.symm)).l, ((haltList tm (u.map oa.symm)).var, none),
        pack tm (haltList tm (u.map oa.symm)).stk ![[], w.reverse, [], []]⟩
      (some ⟨some (Sum.inr 3), (tm.initialState, none),
        pack tm (fun _ => []) ![[], w.reverse, u.reverse, []]⟩) (u.length + 1) := by
    refine ev_congr rfl ?_ (ev_mono hC (by simp))
    have e1 : Function.update (haltList tm (u.map oa.symm)).stk tm.k₁ [] = fun _ => [] := by
      rw [haltList_stk_eq]; simp
    rw [e1]
    simp [Function.comp_def]
  -- stage D
  have hD := mv_run (M := prog ia oa) (src := (Sum.inr 2 : Key tm)) (dst := Sum.inr 3)
    (g := id) (h := id) (self := Sum.inr 3) (next := Sum.inr 4)
    rfl (by simp) u.reverse (tm.initialState, none)
    (pack tm (fun _ => []) ![[], w.reverse, u.reverse, []]) rfl
  simp only [pack_update_inr, pack_inr, upd_vec2, upd_vec3, vec_3, List.append_nil, id,
    List.map_id', List.reverse_reverse] at hD
  -- stage E
  have hE := mv_run (M := prog ia oa) (src := (Sum.inr 1 : Key tm)) (dst := Sum.inr 3)
    (g := id) (h := id) (self := Sum.inr 4) (next := Sum.inr 5)
    rfl (by simp) w.reverse (tm.initialState, none)
    (pack tm (fun _ => []) ![[], w.reverse, [], u]) rfl
  simp only [pack_update_inr, pack_inr, upd_vec1, upd_vec3, vec_3, id,
    List.map_id', List.reverse_reverse] at hE
  -- halt
  have hH : EvalsToInTime (TM2.step (prog ia oa))
      ⟨some (Sum.inr 5), (tm.initialState, none), pack tm (fun _ => []) ![[], [], [], w ++ u]⟩
      (some ⟨none, (tm.initialState, none), pack tm (fun _ => []) ![[], [], [], w ++ u]⟩) 1 :=
    ev_one rfl
  have hall := ev_trans (ev_trans (ev_trans (ev_trans (ev_trans (ev_trans hA hB') hT) hC') hD) hE) hH
  refine ev_mono hall ?_
  simp only [List.length_reverse]
  omega

end TeeCore


set_option autoImplicit false

open Turing StateTransition

namespace TeeCore

variable {tm : FinTM2}

theorem initList_tee (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) (w : List Bool) :
    initList (teeTM tm ia oa) w =
      ⟨some (Sum.inr 0), (tm.initialState, none), pack tm (fun _ => []) ![w, [], [], []]⟩ := by
  simp only [initList]
  congr 1
  funext k
  rcases k with a | i
  · simp [pack]
  · fin_cases i <;> simp [pack]

theorem haltList_tee (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) (w : List Bool) :
    haltList (teeTM tm ia oa) w =
      ⟨none, (tm.initialState, none), pack tm (fun _ => []) ![[], [], [], w]⟩ := by
  simp only [haltList]
  congr 1
  funext k
  rcases k with a | i
  · simp [pack]
  · fin_cases i <;> simp [pack]

end TeeCore

open Polynomial in
/-- **Tee combinator.** A polynomial-time machine computing `f` yields a polynomial-time machine
that keeps its input and appends the output: `ea a ↦ ea a ++ eb (f a)`. -/
theorem Turing.TM2ComputableInPolyTime.tee {α β : Type} {ea : α → List Bool}
    {eb : β → List Bool} {f : α → β} (h : TM2ComputableInPolyTime ea eb f) :
    Nonempty (TM2ComputableInPolyTime ea (fun a => ea a ++ eb (f a)) id) := by
  classical
  refine ⟨⟨⟨TeeCore.teeTM h.tm h.inputAlphabet h.outputAlphabet, Equiv.refl Bool,
    Equiv.refl Bool⟩, h.time + C (2 * h.tm.growth) * h.time + C 5 * X + C 6, ?_⟩⟩
  intro a
  have ha := h.outputsFun a
  simp only [Equiv.invFun_as_coe] at ha
  have hrun := TeeCore.tee_run h.inputAlphabet h.outputAlphabet (ea a) (eb (f a)) _ ha
  have hlen := TM2OutputsInTime.output_length_le ha
  simp only [List.length_map] at hlen
  have hT := ha.steps_le_m
  show TM2OutputsInTime (TeeCore.teeTM h.tm h.inputAlphabet h.outputAlphabet)
    (List.map id (ea a)) (some (List.map id (ea a ++ eb (f a)))) _
  simp only [List.map_id]
  unfold TM2OutputsInTime
  rw [TeeCore.initList_tee, Option.map_some, TeeCore.haltList_tee]
  refine TeeCore.ev_mono hrun ?_
  simp only [eval_add, eval_mul, eval_C, eval_X]
  have : h.time.eval (ea a).length * h.tm.growth ≥ 0 := Nat.zero_le _
  nlinarith [hlen]


theorem solution {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    (h : Turing.TM2ComputableInPolyTime ea eb f) :
    Nonempty (Turing.TM2ComputableInPolyTime ea (fun a => ea a ++ eb (f a)) id) :=
  Turing.TM2ComputableInPolyTime.tee h

