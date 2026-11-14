-- Prove2me | solution 1 for QAlgorithms.DeWolf.clocked_tm2_polytime
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:39:55.590686+00:00
-- url     : https://prove2.me/submissions/abe2c10a-a848-4708-ade7-19a1321ac161

import Mathlib

/-! Clock wrapper for TM2 machines (e261f9b1 K side, sessions 17-18).
A machine `M` on stacks `K` is lifted to stacks `K ⊕ A` (aux stacks `A`, all with alphabet `G`);
aux stack `a0` is a clock. Every `goto` of `M` pops one clock cell; when the clock is empty, or
when `M` halts, control passes to the exit label `X`. So the lifted machine reaches `X` within
`|clock| + 1` steps on EVERY input, and on inputs where `M` halts within `|clock|` steps it reaches
`X` with `M`'s final stacks. Section Drain: a cleanup loop emptying a list of stacks, then
loading a fixed state and halting. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace E261Clock

open Turing

lemma iter_none {α : Type} (f : α → Option α) : ∀ n, (flip bind f)^[n] none = none
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply]; exact iter_none f n

lemma iter_some {α : Type} (f : α → Option α) (n : ℕ) (a : α) :
    (flip bind f)^[n + 1] (some a) = (flip bind f)^[n] (f a) := by
  rw [Function.iterate_succ_apply]; rfl

section Lift

variable {K A : Type} [DecidableEq K] [DecidableEq A] {Γ : K → Type} {G : Type} {Λ Λ' σ : Type}

/-- alphabets with extra aux stacks `A`, each with alphabet `G` -/
abbrev XΓ (Γ : K → Type) (G : Type) (j : K ⊕ A) : Type :=
  Sum.casesOn (motive := fun _ => Type) j Γ (fun _ => G)

example (k : K) : XΓ (A := A) Γ G (.inl k) = Γ k := by with_reducible rfl
example (a : A) : XΓ Γ G (.inr a : K ⊕ A) = G := by with_reducible rfl

/-- stacks of the lifted machine -/
def stkL (S : ∀ k, List (Γ k)) (T : A → List G) : ∀ j : K ⊕ A, List (XΓ Γ G j)
  | .inl k => S k
  | .inr a => T a

@[simp] lemma stkL_inl (S : ∀ k, List (Γ k)) (T : A → List G) (k : K) : stkL S T (.inl k) = S k := rfl
@[simp] lemma stkL_inr (S : ∀ k, List (Γ k)) (T : A → List G) (a : A) : stkL S T (.inr a) = T a := rfl

lemma stkL_update (S : ∀ k, List (Γ k)) (T : A → List G) (k : K) (x : List (Γ k)) :
    Function.update (stkL S T) (.inl k) x = stkL (Function.update S k x) T := by
  funext j
  cases j with
  | inr a => simp [Function.update, stkL]
  | inl j =>
    by_cases h : j = k
    · subst h; simp [Function.update, stkL]
    · simp [Function.update, stkL, h]

lemma stkL_update_inr (S : ∀ k, List (Γ k)) (T : A → List G) (a : A) (x : List G) :
    Function.update (stkL S T) (.inr a) x = stkL (Γ := Γ) S (Function.update T a x) := by
  funext j
  cases j with
  | inl j => simp [Function.update, stkL]
  | inr b =>
    by_cases h : b = a
    · subst h; simp [Function.update, stkL]
    · simp [Function.update, stkL, h]

/-- the lifted statement; `e` embeds labels, `X` is the exit label, `a0` the clock -/
def liftS (e : Λ → Λ') (X : Λ') (a0 : A) : TM2.Stmt Γ Λ σ → TM2.Stmt (XΓ (A := A) Γ G) Λ' (σ × Option G)
  | .push k f q => .push (.inl k) (fun s => f s.1) (liftS e X a0 q)
  | .peek k f q => .peek (.inl k) (fun s v => (f s.1 v, s.2)) (liftS e X a0 q)
  | .pop k f q => .pop (.inl k) (fun s v => (f s.1 v, s.2)) (liftS e X a0 q)
  | .load a q => .load (fun s => (a s.1, s.2)) (liftS e X a0 q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (liftS e X a0 q₁) (liftS e X a0 q₂)
  | .goto f => .pop (.inr a0) (fun s v => (s.1, v))
      (.branch (fun s => s.2.isSome) (.goto fun s => e (f s.1)) (.goto fun _ => X))
  | .halt => .goto fun _ => X

/-- the lifted result of one `stepAux` -/
def liftRes (e : Λ → Λ') (X : Λ') (a0 : A) (c : TM2.Cfg Γ Λ σ) (T : A → List G) (b : Option G) :
    TM2.Cfg (XΓ (A := A) Γ G) Λ' (σ × Option G) :=
  match c.l with
  | none => ⟨some X, (c.var, b), stkL c.stk T⟩
  | some l =>
    match T a0 with
    | [] => ⟨some X, (c.var, none), stkL c.stk (Function.update T a0 [])⟩
    | x :: C' => ⟨some (e l), (c.var, some x), stkL c.stk (Function.update T a0 C')⟩

theorem stepAux_lift (e : Λ → Λ') (X : Λ') (a0 : A) (q : TM2.Stmt Γ Λ σ) :
    ∀ (s : σ) (b : Option G) (S : ∀ k, List (Γ k)) (T : A → List G),
      TM2.stepAux (liftS e X a0 q) (s, b) (stkL S T) = liftRes e X a0 (TM2.stepAux q s S) T b := by
  induction q with
  | push k f q ih =>
    intro s b S T
    simp only [liftS, TM2.stepAux]
    rw [show (f s :: stkL S T (.inl k) : List (XΓ Γ G (.inl k))) = (f s :: S k : List (Γ k)) from rfl,
      stkL_update]
    exact ih s b _ T
  | peek k f q ih =>
    intro s b S T
    simp only [liftS, TM2.stepAux]
    exact ih _ b S T
  | pop k f q ih =>
    intro s b S T
    simp only [liftS, TM2.stepAux]
    rw [show ((stkL S T (.inl k)).tail : List (XΓ Γ G (.inl k))) = ((S k).tail : List (Γ k)) from rfl,
      stkL_update]
    exact ih _ b _ T
  | load a q ih =>
    intro s b S T
    simp only [liftS, TM2.stepAux]
    exact ih _ b S T
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro s b S T
    simp only [liftS, TM2.stepAux]
    cases f s
    · exact ih₂ s b S T
    · exact ih₁ s b S T
  | goto f =>
    intro s b S T
    simp only [liftS, TM2.stepAux, stkL_inr]
    rw [stkL_update_inr]
    cases hT : T a0 with
    | nil => simp [liftRes, hT]
    | cons x C' => simp [liftRes, hT]
  | halt =>
    intro s b S T
    simp only [liftS, TM2.stepAux, liftRes]

/-- lifted configuration of a running machine -/
def liftC (e : Λ → Λ') (c : TM2.Cfg Γ Λ σ) (T : A → List G) (b : Option G) :
    TM2.Cfg (XΓ (A := A) Γ G) Λ' (σ × Option G) :=
  ⟨c.l.map e, (c.var, b), stkL c.stk T⟩

section Sim

variable (M : Λ → TM2.Stmt Γ Λ σ) (M' : Λ' → TM2.Stmt (XΓ (A := A) Γ G) Λ' (σ × Option G))
  (e : Λ → Λ') (X : Λ') (a0 : A)

theorem step_lift (hM : ∀ l, M' (e l) = liftS e X a0 (M l)) (l : Λ) (s : σ) (b : Option G)
    (S : ∀ k, List (Γ k)) (T : A → List G) :
    TM2.step M' (liftC e ⟨some l, s, S⟩ T b) = some (liftRes e X a0 (TM2.stepAux (M l) s S) T b) := by
  simp only [liftC, Option.map_some, TM2.step, hM, stepAux_lift]

/-- if `M` halts after `t + 1` steps and the clock holds at least `t` cells, the lifted machine
reaches the exit label with `M`'s final state and stacks after `t + 1` steps -/
theorem sim_halt (hM : ∀ l, M' (e l) = liftS e X a0 (M l)) :
    ∀ (t : ℕ) (c c' : TM2.Cfg Γ Λ σ) (T : A → List G) (b : Option G),
      (flip bind (TM2.step M))^[t + 1] (some c) = some c' → c'.l = none → t ≤ (T a0).length →
      ∃ (T' : A → List G) (b' : Option G),
        (flip bind (TM2.step M'))^[t + 1] (some (liftC e c T b)) =
          some ⟨some X, (c'.var, b'), stkL c'.stk T'⟩ := by
  intro t
  induction t with
  | zero =>
    intro c c' T b h hl _
    obtain ⟨l, s, S⟩ := c
    rw [iter_some] at h
    cases l with
    | none => simp [TM2.step] at h
    | some l =>
      simp only [Function.iterate_zero, id, TM2.step] at h
      have h' := Option.some.inj h
      refine ⟨T, b, ?_⟩
      rw [iter_some, Function.iterate_zero, id, step_lift M M' e X a0 hM, h']
      simp only [liftRes, hl]
  | succ t ih =>
    intro c c' T b h hl hC
    obtain ⟨l, s, S⟩ := c
    rw [iter_some] at h
    cases l with
    | none =>
      rw [show TM2.step M ⟨none, s, S⟩ = none from rfl, iter_none] at h
      exact absurd h (by simp)
    | some l =>
      simp only [TM2.step] at h
      set c1 := TM2.stepAux (M l) s S with hc1
      obtain ⟨l1, s1, S1⟩ := c1
      cases l1 with
      | none =>
        exfalso
        rw [iter_some, show TM2.step M ⟨none, s1, S1⟩ = none from rfl, iter_none] at h
        exact absurd h (by simp)
      | some l1 =>
        cases hT : T a0 with
        | nil => rw [hT] at hC; simp at hC
        | cons x C' =>
          obtain ⟨T'', b', h2⟩ := ih ⟨some l1, s1, S1⟩ c' (Function.update T a0 C') (some x) h hl
            (by rw [hT] at hC; simpa using hC)
          refine ⟨T'', b', ?_⟩
          rw [iter_some, step_lift M M' e X a0 hM, ← hc1]
          simp only [liftRes, hT]
          exact h2

/-- from any running configuration the lifted machine reaches the exit label within
`|clock| + 1` steps, with the state and stacks of the `M`-configuration at that time -/
theorem reach_exit (hM : ∀ l, M' (e l) = liftS e X a0 (M l)) :
    ∀ (n : ℕ) (T : A → List G), (T a0).length = n → ∀ (l : Λ) (s : σ) (S : ∀ k, List (Γ k)) (b : Option G),
      ∃ t ≤ n, ∃ c1 : TM2.Cfg Γ Λ σ,
        (flip bind (TM2.step M))^[t + 1] (some ⟨some l, s, S⟩) = some c1 ∧
        ∃ (T' : A → List G) (b' : Option G),
          (flip bind (TM2.step M'))^[t + 1] (some (liftC e ⟨some l, s, S⟩ T b)) =
            some ⟨some X, (c1.var, b'), stkL c1.stk T'⟩ := by
  intro n
  induction n with
  | zero =>
    intro T hn l s S b
    have hT : T a0 = [] := List.length_eq_zero_iff.mp hn
    refine ⟨0, le_rfl, TM2.stepAux (M l) s S, rfl, ?_⟩
    rw [iter_some, Function.iterate_zero, id, step_lift M M' e X a0 hM]
    obtain ⟨l1, s1, S1⟩ := TM2.stepAux (M l) s S
    cases l1 with
    | none => exact ⟨T, b, rfl⟩
    | some l1 => exact ⟨Function.update T a0 [], none, by simp [liftRes, hT]⟩
  | succ n ih =>
    intro T hn l s S b
    cases hT : T a0 with
    | nil => rw [hT] at hn; simp at hn
    | cons x C' =>
      rw [hT] at hn
      rcases hc : TM2.stepAux (M l) s S with ⟨l1, s1, S1⟩
      cases l1 with
      | none =>
        refine ⟨0, Nat.zero_le _, ⟨none, s1, S1⟩, ?_, T, b, ?_⟩
        · rw [iter_some, Function.iterate_zero, id]; simp only [TM2.step, hc]
        · rw [iter_some, Function.iterate_zero, id, step_lift M M' e X a0 hM, hc]; rfl
      | some l1 =>
        obtain ⟨t, ht, c1, h1, T', b', h2⟩ :=
          ih (Function.update T a0 C') (by simpa using hn) l1 s1 S1 (some x)
        refine ⟨t + 1, by omega, c1, ?_, T', b', ?_⟩
        · rw [iter_some]; simp only [TM2.step, hc]; exact h1
        · rw [iter_some, step_lift M M' e X a0 hM, hc]
          simp only [liftRes, hT]
          exact h2

end Sim

end Lift

section Drain

variable {J : Type} [DecidableEq J] {Γ' : J → Type} {Λ' σ H : Type}
variable (M' : Λ' → TM2.Stmt Γ' Λ' (σ × Option H)) (js : List J) (dr : Fin (js.length + 1) → Λ')
  (v : σ × Option H) (h0 : H)

/-- drain loop: label `dr i` empties stack `js[i]`, then moves on; the last label loads `v`
and halts -/
def drainS (i : Fin (js.length + 1)) : TM2.Stmt Γ' Λ' (σ × Option H) :=
  if h : (i : ℕ) < js.length then
    .pop js[(i : ℕ)] (fun s w => (s.1, if w.isSome then some h0 else none))
      (.branch (fun s => s.2.isSome) (.goto fun _ => dr i) (.goto fun _ => dr ⟨i + 1, by omega⟩))
  else .load (fun _ => v) .halt

/-- total stack length -/
def tot [Fintype J] (S : ∀ j, List (Γ' j)) : ℕ := ∑ j, (S j).length

lemma tot_update_nil [Fintype J] (S : ∀ j, List (Γ' j)) (j0 : J) :
    tot (Function.update S j0 []) + (S j0).length = tot S := by
  unfold tot
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0), ← Finset.add_sum_erase _ _ (Finset.mem_univ j0)]
  simp only [Function.update_self, List.length_nil, zero_add]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem pop_all (hD : ∀ i, M' (dr i) = drainS js dr v h0 i) (i : ℕ) (hi : i < js.length) :
    ∀ (L : List (Γ' js[i])) (s : σ × Option H) (S : ∀ j, List (Γ' j)), S js[i] = L →
      (flip bind (TM2.step M'))^[L.length + 1] (some ⟨some (dr ⟨i, by omega⟩), s, S⟩) =
        some ⟨some (dr ⟨i + 1, by omega⟩), (s.1, none), Function.update S js[i] []⟩ := by
  intro L
  induction L with
  | nil =>
    intro s S hS
    rw [iter_some, List.length_nil, Function.iterate_zero, id]
    simp [TM2.step, hD, drainS, hi, TM2.stepAux, hS]
  | cons x L ih =>
    intro s S hS
    rw [show (x :: L).length + 1 = (L.length + 1) + 1 from rfl, iter_some]
    have h1 : TM2.step M' ⟨some (dr ⟨i, by omega⟩), s, S⟩ =
        some ⟨some (dr ⟨i, by omega⟩), (s.1, some h0), Function.update S js[i] L⟩ := by
      simp [TM2.step, hD, drainS, hi, TM2.stepAux, hS]
    rw [h1, ih (s.1, some h0) _ (by simp)]
    simp [Function.update_idem]

theorem drain_from [Fintype J] (hD : ∀ i, M' (dr i) = drainS js dr v h0 i) :
    ∀ (n i : ℕ) (hi : i + n = js.length) (s : σ × Option H) (S : ∀ j, List (Γ' j)),
      ∃ t ≤ n + 1 + tot S, ∃ R : ∀ j, List (Γ' j),
        (∀ j ∈ js.drop i, R j = []) ∧ (∀ j, j ∉ js.drop i → R j = S j) ∧
        (flip bind (TM2.step M'))^[t] (some ⟨some (dr ⟨i, by omega⟩), s, S⟩) = some ⟨none, v, R⟩ := by
  intro n
  induction n with
  | zero =>
    intro i hi s S
    have hi' : i = js.length := by omega
    refine ⟨1, by omega, S, ?_, fun _ _ => rfl, ?_⟩
    · intro j hj; subst hi'; simp at hj
    · rw [iter_some, Function.iterate_zero, id]
      have : ¬ (i < js.length) := by omega
      simp [TM2.step, hD, drainS, this, TM2.stepAux]
  | succ n ih =>
    intro i hi s S
    have hlt : i < js.length := by omega
    obtain ⟨t, ht, R, hR1, hR2, hR3⟩ := ih (i + 1) (by omega) (s.1, none) (Function.update S js[i] [])
    have hp := pop_all M' js dr v h0 hD i hlt (S js[i]) s S rfl
    have htot := tot_update_nil S js[i]
    refine ⟨t + ((S js[i]).length + 1), ?_, R, ?_, ?_, ?_⟩
    · have : (S js[i]).length ≤ tot S := by omega
      omega
    · intro j hj
      rw [List.drop_eq_getElem_cons hlt] at hj
      rcases List.mem_cons.mp hj with h | h
      · by_cases h' : j ∈ js.drop (i + 1)
        · exact hR1 j h'
        · rw [hR2 j h', h]; simp
      · exact hR1 j h
    · intro j hj
      rw [List.drop_eq_getElem_cons hlt] at hj
      have h1 : j ≠ js[i] := fun h => hj (by rw [h]; exact List.mem_cons_self)
      have h2 : j ∉ js.drop (i + 1) := fun h => hj (List.mem_cons_of_mem _ h)
      rw [hR2 j h2, Function.update_of_ne h1]
    · rw [Function.iterate_add_apply, hp]
      exact hR3

end Drain

section Growth

variable {J : Type} [DecidableEq J] {Γ' : J → Type} {Λ σ : Type}

/-- maximal number of pushes along any path of a statement -/
def pushCount : TM2.Stmt Γ' Λ σ → ℕ
  | .push _ _ q => pushCount q + 1
  | .peek _ _ q => pushCount q
  | .pop _ _ q => pushCount q
  | .load _ q => pushCount q
  | .branch _ q₁ q₂ => max (pushCount q₁) (pushCount q₂)
  | .goto _ => 0
  | .halt => 0

lemma tot_update [Fintype J] (S : ∀ j, List (Γ' j)) (j0 : J) (L : List (Γ' j0)) :
    tot (Function.update S j0 L) + (S j0).length = tot S + L.length := by
  unfold tot
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0), ← Finset.add_sum_erase _ _ (Finset.mem_univ j0)]
  simp only [Function.update_self]
  have : ∑ j ∈ Finset.univ.erase j0, (Function.update S j0 L j).length =
      ∑ j ∈ Finset.univ.erase j0, (S j).length :=
    Finset.sum_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  rw [this]; ring

lemma tot_stepAux [Fintype J] (q : TM2.Stmt Γ' Λ σ) :
    ∀ (s : σ) (S : ∀ j, List (Γ' j)), tot (TM2.stepAux q s S).stk ≤ tot S + pushCount q := by
  induction q with
  | push k f q ih =>
    intro s S
    simp only [TM2.stepAux, pushCount]
    have h1 := tot_update S k (f s :: S k)
    have h2 := ih s (Function.update S k (f s :: S k))
    simp only [List.length_cons] at h1
    omega
  | peek k f q ih =>
    intro s S
    simp only [TM2.stepAux, pushCount]
    exact ih _ S
  | pop k f q ih =>
    intro s S
    simp only [TM2.stepAux, pushCount]
    have h1 := tot_update S k (S k).tail
    have h2 := ih (f s (S k).head?) (Function.update S k (S k).tail)
    have h3 : (S k).tail.length ≤ (S k).length := by simp
    omega
  | load a q ih =>
    intro s S
    simp only [TM2.stepAux, pushCount]
    exact ih _ S
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro s S
    simp only [TM2.stepAux, pushCount]
    cases f s
    · exact (ih₂ s S).trans (Nat.add_le_add_left (le_max_right _ _) _)
    · exact (ih₁ s S).trans (Nat.add_le_add_left (le_max_left _ _) _)
  | goto f =>
    intro s S
    simp [TM2.stepAux]
  | halt =>
    intro s S
    simp [TM2.stepAux]

/-- per-step push bound of a machine -/
def pushMax [Fintype Λ] (M : Λ → TM2.Stmt Γ' Λ σ) : ℕ := Finset.univ.sup fun l => pushCount (M l)

theorem tot_iter [Fintype J] [Fintype Λ] (M : Λ → TM2.Stmt Γ' Λ σ) :
    ∀ (n : ℕ) (c c' : TM2.Cfg Γ' Λ σ), (flip bind (TM2.step M))^[n] (some c) = some c' →
      tot c'.stk ≤ tot c.stk + n * pushMax M := by
  intro n
  induction n with
  | zero =>
    intro c c' h
    simp only [Function.iterate_zero, id, Option.some.injEq] at h
    subst h; simp
  | succ n ih =>
    intro c c' h
    obtain ⟨l, s, S⟩ := c
    rw [iter_some] at h
    cases l with
    | none =>
      rw [show TM2.step M ⟨none, s, S⟩ = none from rfl, iter_none] at h
      exact absurd h (by simp)
    | some l =>
      have h1 := ih _ c' h
      have h2 := tot_stepAux (M l) s S
      have h3 : pushCount (M l) ≤ pushMax M := Finset.le_sup (f := fun l => pushCount (M l)) (Finset.mem_univ l)
      rw [add_mul, one_mul]
      simp only at h1 h2 ⊢
      omega

end Growth

section Move

variable {K A : Type} [DecidableEq K] [DecidableEq A] {Γ : K → Type} {G : Type} {Λ' σ : Type}
variable (M' : Λ' → TM2.Stmt (XΓ (A := A) Γ G) Λ' (σ × Option G)) (g0 : G)

/-- move all cells of aux stack `src` onto aux stack `dst` (reversing), pushing one `g0` cell on
`cnt` (if given) per moved cell -/
def moveS (src dst : A) (cnt : Option A) (here next : Λ') :
    TM2.Stmt (XΓ (A := A) Γ G) Λ' (σ × Option G) :=
  .pop (.inr src) (fun s v => (s.1, v))
    (.branch (fun s => s.2.isSome)
      (.push (.inr dst) (fun s => s.2.getD g0)
        (match cnt with
         | none => .goto fun _ => here
         | some c => .push (.inr c) (fun _ => g0) (.goto fun _ => here)))
      (.goto fun _ => next))

/-- aux stacks after a full move -/
def moveT (src dst : A) (cnt : Option A) (L : List G) (T : A → List G) : A → List G :=
  fun a => if a = src then [] else if a = dst then L.reverse ++ T a
    else if some a = cnt then List.replicate L.length g0 ++ T a else T a

variable (src dst : A) (cnt : Option A) (here next : Λ')

lemma move_step_nil (hm : M' here = moveS g0 src dst cnt here next) (s : σ × Option G)
    (S : ∀ k, List (Γ k)) (T : A → List G) (hT : T src = []) :
    TM2.step M' ⟨some here, s, stkL S T⟩ = some ⟨some next, (s.1, none), stkL S T⟩ := by
  rw [show TM2.step M' ⟨some here, s, stkL S T⟩ = some (TM2.stepAux (M' here) s (stkL S T)) from rfl, hm]
  simp only [moveS, TM2.stepAux, stkL_inr, hT, List.head?_nil, List.tail_nil, Option.isSome_none,
    cond_false, stkL_update_inr]
  rw [← hT, Function.update_eq_self]

lemma move_step_cons (hm : M' here = moveS g0 src dst cnt here next) (hsd : src ≠ dst)
    (hsc : cnt ≠ some src) (hdc : cnt ≠ some dst) (s : σ × Option G) (S : ∀ k, List (Γ k))
    (T : A → List G) (x : G) (L : List G) (hT : T src = x :: L) :
    TM2.step M' ⟨some here, s, stkL S T⟩ = some ⟨some here, (s.1, some x), stkL S (fun a =>
      if a = src then L else if a = dst then x :: T a else if some a = cnt then g0 :: T a else T a)⟩ := by
  rw [show TM2.step M' ⟨some here, s, stkL S T⟩ = some (TM2.stepAux (M' here) s (stkL S T)) from rfl, hm]
  cases cnt with
  | none =>
    simp only [moveS, TM2.stepAux, stkL_inr, hT, List.head?_cons, List.tail_cons, Option.isSome_some,
      cond_true, stkL_update_inr, Option.getD_some]
    congr 3
    funext a
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  | some c =>
    simp only [moveS, TM2.stepAux, stkL_inr, hT, List.head?_cons, List.tail_cons, Option.isSome_some,
      cond_true, stkL_update_inr, Option.getD_some]
    congr 3
    funext a
    simp only [Function.update_apply]
    split_ifs <;> simp_all

theorem move_run (hm : M' here = moveS g0 src dst cnt here next) (hsd : src ≠ dst)
    (hsc : cnt ≠ some src) (hdc : cnt ≠ some dst) :
    ∀ (L : List G) (s : σ × Option G) (S : ∀ k, List (Γ k)) (T : A → List G), T src = L →
      (flip bind (TM2.step M'))^[L.length + 1] (some ⟨some here, s, stkL S T⟩) =
        some ⟨some next, (s.1, none), stkL S (moveT g0 src dst cnt L T)⟩ := by
  intro L
  induction L with
  | nil =>
    intro s S T hT
    rw [iter_some, List.length_nil, Function.iterate_zero, id, move_step_nil M' g0 src dst cnt here next hm s S T hT]
    congr 3
    funext a
    by_cases h : a = src
    · subst h; simp [moveT, hT]
    · simp [moveT, h]
  | cons x L ih =>
    intro s S T hT
    rw [show (x :: L).length + 1 = (L.length + 1) + 1 from rfl, iter_some,
      move_step_cons M' g0 src dst cnt here next hm hsd hsc hdc s S T x L hT, ih _ _ _ (by simp)]
    congr 3
    funext a
    simp only [moveT]
    by_cases h1 : a = src
    · simp [h1]
    · by_cases h2 : a = dst
      · subst h2; simp [h1, hsd]
      · by_cases h3 : some a = cnt
        · simp [h1, h2, h3, List.replicate_succ']
        · simp [h1, h2, h3]

end Move

section Mul

variable {K A : Type} [DecidableEq K] [DecidableEq A] {Γ : K → Type} {G : Type} {Λ' σ : Type}
variable (M' : Λ' → TM2.Stmt (XΓ (A := A) Γ G) Λ' (σ × Option G)) (g0 : G)

/-- pop one cell of aux stack `y`; go to `yes` if there was one, else to `no` -/
def popS (y : A) (yes no : Λ') : TM2.Stmt (XΓ (A := A) Γ G) Λ' (σ × Option G) :=
  .pop (.inr y) (fun s v => (s.1, v)) (.branch (fun s => s.2.isSome) (.goto fun _ => yes) (.goto fun _ => no))

variable (y : A) (yes no : Λ')

lemma pop_step_nil (hp : M' yes = popS y yes no ∨ True) (here : Λ') (hh : M' here = popS y yes no)
    (s : σ × Option G) (S : ∀ k, List (Γ k)) (T : A → List G) (hT : T y = []) :
    TM2.step M' ⟨some here, s, stkL S T⟩ = some ⟨some no, (s.1, none), stkL S T⟩ := by
  rw [show TM2.step M' ⟨some here, s, stkL S T⟩ = some (TM2.stepAux (M' here) s (stkL S T)) from rfl, hh]
  simp only [popS, TM2.stepAux, stkL_inr, hT, List.head?_nil, List.tail_nil, Option.isSome_none,
    cond_false, stkL_update_inr]
  rw [← hT, Function.update_eq_self]

lemma pop_step_cons (here : Λ') (hh : M' here = popS y yes no)
    (s : σ × Option G) (S : ∀ k, List (Γ k)) (T : A → List G) (c : G) (L : List G) (hT : T y = c :: L) :
    TM2.step M' ⟨some here, s, stkL S T⟩ = some ⟨some yes, (s.1, some c), stkL S (Function.update T y L)⟩ := by
  rw [show TM2.step M' ⟨some here, s, stkL S T⟩ = some (TM2.stepAux (M' here) s (stkL S T)) from rfl, hh]
  simp only [popS, TM2.stepAux, stkL_inr, hT, List.head?_cons, List.tail_cons, Option.isSome_some,
    cond_true, stkL_update_inr]

variable (x xt z : A) (m0 m1 m2 next : Λ')

/-- unary multiply: `z += |y| * |x|` cells, `y` emptied, `x` kept (`xt` empty temp) -/
theorem mul_run (h0 : M' m0 = popS y m1 next) (h1 : M' m1 = moveS g0 x xt (some z) m1 m2)
    (h2 : M' m2 = moveS g0 xt x none m2 m0)
    (hxxt : x ≠ xt) (hxy : x ≠ y) (hxz : x ≠ z) (hxty : xt ≠ y) (hxtz : xt ≠ z) (hyz : y ≠ z) :
    ∀ (Ly : List G) (s : σ × Option G) (S : ∀ k, List (Γ k)) (T : A → List G), T y = Ly → T xt = [] →
      (flip bind (TM2.step M'))^[Ly.length * (2 * (T x).length + 3) + 1] (some ⟨some m0, s, stkL S T⟩) =
        some ⟨some next, (s.1, none), stkL S (fun a => if a = y then [] else
          if a = z then List.replicate (Ly.length * (T x).length) g0 ++ T a else T a)⟩ := by
  intro Ly
  induction Ly with
  | nil =>
    intro s S T hy hxt
    rw [List.length_nil, zero_mul, zero_add, iter_some, Function.iterate_zero, id,
      pop_step_nil M' y m1 next (Or.inr trivial) m0 h0 s S T hy]
    congr 3
    funext a
    by_cases h : a = y
    · subst h; simp [hy]
    · simp [h]
  | cons c Ly ih =>
    intro s S T hy hxt
    have e1 := pop_step_cons M' y m1 next m0 h0 s S T c Ly hy
    have e2 := move_run M' g0 x xt (some z) m1 m2 h1 hxxt (by simp [Ne.symm hxz]) (by simp [Ne.symm hxtz])
      (T x) (s.1, some c) S (Function.update T y Ly) (by simp [hxy])
    have e3 := move_run M' g0 xt x none m2 m0 h2 (Ne.symm hxxt) (by simp) (by simp)
      (T x).reverse (s.1, none) S (moveT g0 x xt (some z) (T x) (Function.update T y Ly))
      (by simp [moveT, Ne.symm hxxt, hxty, hxt])
    dsimp only at e2 e3
    have hy3 : moveT g0 xt x none (T x).reverse (moveT g0 x xt (some z) (T x) (Function.update T y Ly)) y = Ly := by
      simp [moveT, Ne.symm hxty, Ne.symm hxy, hyz]
    have hxt3 : moveT g0 xt x none (T x).reverse (moveT g0 x xt (some z) (T x) (Function.update T y Ly)) xt = [] := by
      simp [moveT]
    have hx3 : moveT g0 xt x none (T x).reverse (moveT g0 x xt (some z) (T x) (Function.update T y Ly)) x = T x := by
      simp [moveT, hxxt]
    have e4 := ih (s.1, none) S _ hy3 hxt3
    rw [hx3] at e4
    rw [show (c :: Ly).length * (2 * (T x).length + 3) + 1 =
        ((Ly.length * (2 * (T x).length + 3) + 1) + ((T x).reverse.length + 1) + ((T x).length + 1)) + 1 by
          simp only [List.length_reverse, List.length_cons]; ring,
      iter_some, e1, Function.iterate_add_apply, Function.iterate_add_apply, e2, e3, e4]
    congr 3
    funext a
    by_cases ha1 : a = y
    · simp [ha1]
    · by_cases ha2 : a = z
      · subst ha2
        simp [ha1, moveT, Ne.symm hxz, Ne.symm hxtz, add_mul, ← List.append_assoc, List.replicate_append_replicate]
      · by_cases ha3 : a = x
        · subst ha3; simp [ha1, ha2, moveT, hxxt]
        · by_cases ha4 : a = xt
          · subst ha4; simp [ha1, ha2, ha3, moveT, hxt]
          · simp [ha1, ha2, ha3, ha4, moveT]

end Mul

section PushRep

/-- push `n` copies of `g` on aux stack `j`, then run `q` -/
def pushRep {K A : Type} {Γ : K → Type} {G Λ' τ : Type} (j : A) (g : G) :
    ℕ → TM2.Stmt (XΓ (A := A) Γ G) Λ' τ → TM2.Stmt (XΓ (A := A) Γ G) Λ' τ
  | 0, q => q
  | n + 1, q => .push (.inr j) (fun _ => g) (pushRep j g n q)

lemma stepAux_pushRep {K A : Type} [DecidableEq K] [DecidableEq A] {Γ : K → Type} {G Λ' τ : Type}
    (j : A) (g : G) (q : TM2.Stmt (XΓ (A := A) Γ G) Λ' τ) :
    ∀ (n : ℕ) (s : τ) (S : ∀ k, List (Γ k)) (T : A → List G),
      TM2.stepAux (pushRep j g n q) s (stkL S T) =
        TM2.stepAux q s (stkL S (Function.update T j (List.replicate n g ++ T j))) := by
  intro n
  induction n with
  | zero => intro s S T; simp [pushRep]
  | succ n ih =>
    intro s S T
    simp only [pushRep, TM2.stepAux, stkL_inr]
    rw [stkL_update_inr, ih]
    simp only [Function.update_idem, Function.update_self, List.replicate_succ', List.append_assoc,
      List.singleton_append]

end PushRep

section Robust

/-- all stacks except the output stack -/
noncomputable def jsL {K : Type} [DecidableEq K] [Fintype K] (k1 : K) : List (K ⊕ Fin 5) :=
  (Finset.univ.filter (fun j => j ≠ Sum.inl k1)).toList

lemma mem_jsL {K : Type} [DecidableEq K] [Fintype K] (k1 : K) (j : K ⊕ Fin 5) :
    j ∈ jsL k1 ↔ j ≠ Sum.inl k1 := by simp [jsL]

/-- labels of the composite machine: init (start/count/restore), multiply rounds, `M`, drain -/
abbrev LC {K : Type} [DecidableEq K] [Fintype K] (Λ : Type) (k1 : K) (d : ℕ) : Type :=
  (Option Bool ⊕ (Bool × Bool) × Fin d) ⊕ Λ ⊕ Fin ((jsL k1).length + 1)

variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} (k0 k1 : K) [Inhabited (Γ k0)]
  {Λ σ : Type} (M : Λ → TM2.Stmt Γ Λ σ) (main : Λ) (c d : ℕ) (s0 : σ)

/-- label after multiply round `i - 1` -/
def nxt (i : ℕ) : LC Λ k1 d :=
  if h : i < d then .inl (.inr ((false, false), ⟨i, h⟩)) else .inr (.inl main)

/-- the composite program. Aux stacks: 0 clock/product, 1 counter `N`, 2 temp, 3 product temp,
4 input copy -/
noncomputable def prog : LC Λ k1 d →
    TM2.Stmt (XΓ (A := Fin 5) Γ (Option (Γ k0))) (LC Λ k1 d) (σ × Option (Option (Γ k0)))
  | .inl (.inl none) => pushRep (1 : Fin 5) none c
      (.push (.inr 0) (fun _ => none) (.goto fun _ => .inl (.inl (some false))))
  | .inl (.inl (some false)) => .pop (.inl k0) (fun s v => (s.1, v.map fun x => (some x : Option (Γ k0))))
      (.branch (fun s => s.2.isSome)
        (.push (.inr 4) (fun s => s.2.getD none) (.push (.inr 1) (fun _ => none)
          (.goto fun _ => .inl (.inl (some false)))))
        (.goto fun _ => .inl (.inl (some true))))
  | .inl (.inl (some true)) => .pop (.inr 4) (fun s v => (s.1, v))
      (.branch (fun s => s.2.isSome)
        (.push (.inl k0) (fun s => ((s.2.getD none).getD default : Γ k0))
          (.goto fun _ => .inl (.inl (some true))))
        (.goto fun _ => nxt k1 main d 0))
  | .inl (.inr ((false, false), i)) => popS 0 (.inl (.inr ((false, true), i))) (.inl (.inr ((true, true), i)))
  | .inl (.inr ((false, true), i)) =>
      moveS none 1 2 (some 3) (.inl (.inr ((false, true), i))) (.inl (.inr ((true, false), i)))
  | .inl (.inr ((true, false), i)) =>
      moveS none 2 1 none (.inl (.inr ((true, false), i))) (.inl (.inr ((false, false), i)))
  | .inl (.inr ((true, true), i)) =>
      moveS none 3 0 none (.inl (.inr ((true, true), i))) (nxt k1 main d (i.1 + 1))
  | .inr (.inl l) => liftS (fun l => .inr (.inl l)) (.inr (.inr ⟨0, Nat.succ_pos _⟩)) (0 : Fin 5) (M l)
  | .inr (.inr i) => drainS (jsL k1) (fun i => .inr (.inr i)) (s0, none) none i

theorem start_step (s : σ × Option (Option (Γ k0))) (S : ∀ k, List (Γ k))
    (P N X Q Tm : List (Option (Γ k0))) :
    TM2.step (prog k0 k1 M main c d s0) ⟨some (.inl (.inl none)), s, stkL S ![P, N, X, Q, Tm]⟩ =
      some ⟨some (.inl (.inl (some false))), s,
        stkL S ![none :: P, List.replicate c none ++ N, X, Q, Tm]⟩ := by
  rw [show TM2.step (prog k0 k1 M main c d s0) ⟨some (.inl (.inl none)), s, stkL S ![P, N, X, Q, Tm]⟩ =
    some (TM2.stepAux (prog k0 k1 M main c d s0 (.inl (.inl none))) s (stkL S ![P, N, X, Q, Tm])) from rfl]
  simp only [prog, stepAux_pushRep, TM2.stepAux, stkL_inr, stkL_update_inr]
  congr 3
  funext a
  fin_cases a <;> rfl

theorem cnt_run : ∀ (L : List (Γ k0)) (s : σ × Option (Option (Γ k0))) (S : ∀ k, List (Γ k))
    (P N X Q Tm : List (Option (Γ k0))), S k0 = L →
    (flip bind (TM2.step (prog k0 k1 M main c d s0)))^[L.length + 1]
      (some ⟨some (.inl (.inl (some false))), s, stkL S ![P, N, X, Q, Tm]⟩) =
    some ⟨some (.inl (.inl (some true))), (s.1, none),
      stkL (Function.update S k0 []) ![P, List.replicate L.length none ++ N, X, Q,
        L.reverse.map some ++ Tm]⟩ := by
  intro L
  induction L with
  | nil =>
    intro s S P N X Q Tm hS
    rw [iter_some, List.length_nil, Function.iterate_zero, id]
    rw [show TM2.step (prog k0 k1 M main c d s0) ⟨some (.inl (.inl (some false))), s, stkL S ![P, N, X, Q, Tm]⟩ =
      some (TM2.stepAux (prog k0 k1 M main c d s0 (.inl (.inl (some false)))) s (stkL S ![P, N, X, Q, Tm])) from rfl]
    simp [prog, TM2.stepAux, hS, stkL_update]
  | cons x L ih =>
    intro s S P N X Q Tm hS
    have h1 : TM2.step (prog k0 k1 M main c d s0)
        ⟨some (.inl (.inl (some false))), s, stkL S ![P, N, X, Q, Tm]⟩ =
        some ⟨some (.inl (.inl (some false))), (s.1, some (some x)),
          stkL (Function.update S k0 L) ![P, none :: N, X, Q, some x :: Tm]⟩ := by
      rw [show TM2.step (prog k0 k1 M main c d s0) ⟨some (.inl (.inl (some false))), s, stkL S ![P, N, X, Q, Tm]⟩ =
        some (TM2.stepAux (prog k0 k1 M main c d s0 (.inl (.inl (some false)))) s (stkL S ![P, N, X, Q, Tm])) from rfl]
      simp only [prog, TM2.stepAux, stkL_inl, hS, List.head?_cons, List.tail_cons, Option.map_some,
        Option.isSome_some, cond_true, stkL_update, stkL_inr, stkL_update_inr, Option.getD_some]
      congr 3
      funext a
      fin_cases a <;> rfl
    rw [show (x :: L).length + 1 = (L.length + 1) + 1 from rfl, iter_some, h1,
      ih (s.1, some (some x)) (Function.update S k0 L) P (none :: N) X Q (some x :: Tm) (by simp)]
    simp [Function.update_idem, List.replicate_succ']

theorem rst_run : ∀ (L : List (Γ k0)) (s1 : σ) (b : Option (Option (Γ k0))) (S : ∀ k, List (Γ k))
    (P N X Q : List (Option (Γ k0))),
    (flip bind (TM2.step (prog k0 k1 M main c d s0)))^[L.length + 1]
      (some ⟨some (.inl (.inl (some true))), (s1, b), stkL S ![P, N, X, Q, L.map some]⟩) =
    some ⟨some (nxt k1 main d 0), (s1, none),
      stkL (Function.update S k0 (L.reverse ++ S k0)) ![P, N, X, Q, []]⟩ := by
  intro L
  induction L with
  | nil =>
    intro s1 b S P N X Q
    rw [iter_some, List.length_nil, Function.iterate_zero, id]
    rw [show TM2.step (prog k0 k1 M main c d s0) ⟨some (.inl (.inl (some true))), (s1, b), stkL S ![P, N, X, Q, [].map some]⟩ =
      some (TM2.stepAux (prog k0 k1 M main c d s0 (.inl (.inl (some true)))) (s1, b) (stkL S ![P, N, X, Q, [].map some])) from rfl]
    have h4 : (![P, N, X, Q, []] : Fin 5 → List (Option (Γ k0))) 4 = [] := rfl
    have hU : Function.update (![P, N, X, Q, []] : Fin 5 → List (Option (Γ k0))) 4 [] = ![P, N, X, Q, []] := by
      funext a; fin_cases a <;> rfl
    simp only [prog, TM2.stepAux, stkL_inr, List.map_nil, List.reverse_nil, List.nil_append,
      Function.update_eq_self, stkL_update_inr, h4, List.head?_nil, List.tail_nil, Option.isSome_none,
      cond_false, hU]
  | cons x L ih =>
    intro s1 b S P N X Q
    have h1 : TM2.step (prog k0 k1 M main c d s0)
        ⟨some (.inl (.inl (some true))), (s1, b), stkL S ![P, N, X, Q, (x :: L).map some]⟩ =
        some ⟨some (.inl (.inl (some true))), (s1, some (some x)),
          stkL (Function.update S k0 (x :: S k0)) ![P, N, X, Q, L.map some]⟩ := by
      rw [show TM2.step (prog k0 k1 M main c d s0) ⟨some (.inl (.inl (some true))), (s1, b), stkL S ![P, N, X, Q, (x :: L).map some]⟩ =
        some (TM2.stepAux (prog k0 k1 M main c d s0 (.inl (.inl (some true)))) (s1, b) (stkL S ![P, N, X, Q, (x :: L).map some])) from rfl]
      simp only [prog, TM2.stepAux, stkL_inr, stkL_update_inr, stkL_inl, stkL_update]
      simp only [Matrix.cons_val, List.map_cons, List.head?_cons, List.tail_cons, Option.isSome_some,
        cond_true, Option.getD_some]
      congr 3
      funext a
      fin_cases a <;> rfl
    rw [show (x :: L).length + 1 = (L.length + 1) + 1 from rfl, iter_some, h1, ih]
    simp [Function.update_idem]

theorem round_run (i : Fin d) (s1 : σ) (b : Option (Option (Γ k0))) (S : ∀ k, List (Γ k)) (p : ℕ)
    (N Tm : List (Option (Γ k0))) :
    (flip bind (TM2.step (prog k0 k1 M main c d s0)))^[(p * N.length + 1) + (p * (2 * N.length + 3) + 1)]
      (some ⟨some (.inl (.inr ((false, false), i))), (s1, b),
        stkL S ![List.replicate p none, N, [], [], Tm]⟩) =
    some ⟨some (nxt k1 main d (i.1 + 1)), (s1, none),
      stkL S ![List.replicate (p * N.length) none, N, [], [], Tm]⟩ := by
  have e1 := mul_run (prog k0 k1 M main c d s0) (none : Option (Γ k0)) (0 : Fin 5) (1 : Fin 5) 2 3
    (.inl (.inr ((false, false), i))) (.inl (.inr ((false, true), i))) (.inl (.inr ((true, false), i)))
    (.inl (.inr ((true, true), i))) rfl rfl rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (List.replicate p none) (s1, b) S ![List.replicate p none, N, [], [], Tm] rfl rfl
  have hx : (![List.replicate p none, N, [], [], Tm] : Fin 5 → List (Option (Γ k0))) 1 = N := rfl
  rw [hx, List.length_replicate] at e1
  have e2 := move_run (prog k0 k1 M main c d s0) (none : Option (Γ k0)) (3 : Fin 5) 0 none
    (.inl (.inr ((true, true), i))) (nxt k1 main d (i.1 + 1)) rfl (by decide) (by simp) (by simp)
    (List.replicate (p * N.length) none) (s1, none) S
    (fun a => if a = 0 then [] else if a = 3 then List.replicate (p * N.length) none ++
      (![List.replicate p none, N, [], [], Tm] : Fin 5 → List (Option (Γ k0))) a else
      (![List.replicate p none, N, [], [], Tm] : Fin 5 → List (Option (Γ k0))) a) (by simp)
  rw [List.length_replicate] at e2
  rw [Function.iterate_add_apply, e1, e2]
  congr 3
  funext a
  fin_cases a <;> simp [moveT]

theorem rounds_run (s1 : σ) (S : ∀ k, List (Γ k)) (N Tm : List (Option (Γ k0))) :
    ∀ k i, i + k = d → ∃ t ≤ k * ((N.length + 1) ^ d * (3 * N.length + 3) + 2),
      (flip bind (TM2.step (prog k0 k1 M main c d s0)))^[t]
        (some ⟨some (nxt k1 main d i), (s1, none), stkL S ![List.replicate (N.length ^ i) none, N, [], [], Tm]⟩) =
      some ⟨some (.inr (.inl main)), (s1, none),
        stkL S ![List.replicate (N.length ^ d) none, N, [], [], Tm]⟩ := by
  intro k
  induction k with
  | zero =>
    intro i hi
    obtain rfl : i = d := by omega
    refine ⟨0, by simp, ?_⟩
    simp [nxt]
  | succ k ih =>
    intro i hi
    have hid : i < d := by omega
    have hn : nxt k1 main d i = .inl (.inr ((false, false), ⟨i, hid⟩)) := by simp [nxt, hid]
    obtain ⟨t, ht, h⟩ := ih (i + 1) (by omega)
    refine ⟨t + ((N.length ^ i * N.length + 1) + (N.length ^ i * (2 * N.length + 3) + 1)), ?_, ?_⟩
    · have hp : N.length ^ i ≤ (N.length + 1) ^ d :=
        (Nat.pow_le_pow_left (by omega) i).trans (Nat.pow_le_pow_right (by omega) hid.le)
      have h3 := Nat.mul_le_mul_right (3 * N.length + 3) hp
      have e : N.length ^ i * N.length + 1 + (N.length ^ i * (2 * N.length + 3) + 1) =
          N.length ^ i * (3 * N.length + 3) + 2 := by ring
      calc t + (N.length ^ i * N.length + 1 + (N.length ^ i * (2 * N.length + 3) + 1))
          = t + (N.length ^ i * (3 * N.length + 3) + 2) := by rw [e]
        _ ≤ k * ((N.length + 1) ^ d * (3 * N.length + 3) + 2) +
            ((N.length + 1) ^ d * (3 * N.length + 3) + 2) := Nat.add_le_add ht (Nat.add_le_add_right h3 2)
        _ = (k + 1) * ((N.length + 1) ^ d * (3 * N.length + 3) + 2) := by ring
    · rw [Function.iterate_add_apply, hn, round_run k0 k1 M main c d s0 ⟨i, hid⟩ s1 none S (N.length ^ i) N Tm,
        ← pow_succ]
      exact h

theorem init_run (s1 : σ) (w : List (Γ k0)) :
    ∃ t ≤ 2 * w.length + 3 + d * ((w.length + c + 1) ^ d * (3 * (w.length + c) + 3) + 2),
      (flip bind (TM2.step (prog k0 k1 M main c d s0)))^[t]
        (some ⟨some (.inl (.inl none)), (s1, none),
          stkL (Function.update (fun k => ([] : List (Γ k))) k0 w) ![[], [], [], [], []]⟩) =
      some ⟨some (.inr (.inl main)), (s1, none), stkL (Function.update (fun k => ([] : List (Γ k))) k0 w)
        ![List.replicate ((w.length + c) ^ d) none, List.replicate w.length none ++ List.replicate c none,
          [], [], []]⟩ := by
  obtain ⟨t, ht, h⟩ := rounds_run k0 k1 M main c d s0 s1 (Function.update (fun k => ([] : List (Γ k))) k0 w)
    (List.replicate w.length none ++ List.replicate c none) [] d 0 (by omega)
  have hN : (List.replicate w.length (none : Option (Γ k0)) ++ List.replicate c none).length = w.length + c := by
    simp
  rw [hN] at ht h
  simp only [pow_zero, List.replicate_one] at h
  refine ⟨t + ((w.reverse.length + 1) + ((w.length + 1) + 1)), ?_, ?_⟩
  · rw [List.length_reverse]; omega
  · rw [Function.iterate_add_apply _ t, Function.iterate_add_apply _ (w.reverse.length + 1),
      Function.iterate_add_apply _ (w.length + 1) 1,
      show ∀ x, (flip bind (TM2.step (prog k0 k1 M main c d s0)))^[1] (some x) =
        TM2.step (prog k0 k1 M main c d s0) x from fun x => rfl,
      start_step, cnt_run k0 k1 M main c d s0 w _ _ _ _ _ _ _ (by simp)]
    simp only [List.append_nil]
    rw [rst_run]
    simp only [Function.update_idem, Function.update_self, List.reverse_reverse, List.append_nil]
    exact h

lemma tot_stkL {A : Type} [DecidableEq A] [Fintype A] {G : Type} (S : ∀ k, List (Γ k)) (T : A → List G) :
    tot (stkL S T) = (∑ k, (S k).length) + ∑ a, (T a).length := by
  unfold tot; rw [Fintype.sum_sum_type]; rfl

/-- the composite machine -/
noncomputable def compTM [Fintype Λ] [Fintype σ] [Fintype (Γ k0)] : FinTM2 where
  K := K ⊕ Fin 5
  k₀ := Sum.inl k0
  k₁ := Sum.inl k1
  Γ := XΓ (A := Fin 5) Γ (Option (Γ k0))
  Λ := LC Λ k1 d
  main := Sum.inl (Sum.inl none)
  σ := σ × Option (Option (Γ k0))
  initialState := (s0, none)
  Γk₀Fin := (inferInstance : Fintype (Γ k0))
  m := prog k0 k1 M main c d s0

theorem exit_halt [Fintype Λ] [Fintype σ] [Fintype (Γ k0)] (s : σ × Option (Option (Γ k0)))
    (S : ∀ j : K ⊕ Fin 5, List (XΓ (A := Fin 5) Γ (Option (Γ k0)) j)) :
    ∃ t ≤ (jsL k1).length + 1 + tot S,
      (flip bind (TM2.step (prog k0 k1 M main c d s0)))^[t]
        (some ⟨some (.inr (.inr ⟨0, Nat.succ_pos _⟩)), s, S⟩) =
        some (haltList (compTM k0 k1 M main c d s0) (S (.inl k1))) := by
  obtain ⟨t, ht, R, hR1, hR2, hR3⟩ := drain_from (prog k0 k1 M main c d s0) (jsL k1)
    (fun i => .inr (.inr i)) ((s0, none) : σ × Option (Option (Γ k0))) (none : Option (Γ k0))
    (fun _ => rfl) (jsL k1).length 0 (by simp) s S
  refine ⟨t, by simpa using ht, ?_⟩
  have hH : haltList (compTM k0 k1 M main c d s0) (S (.inl k1)) = ⟨none, (s0, none), R⟩ := by
    unfold haltList
    congr 1
    funext j
    by_cases h : j = .inl k1
    · subst h
      exact (dif_pos rfl).trans (hR2 _ (by simp [mem_jsL])).symm
    · exact (dif_neg h).trans (hR1 j ((mem_jsL k1 j).mpr h)).symm
  rw [hH]
  exact hR3

/-- the composite time bound -/
noncomputable def Bnd [Fintype Λ] (n : ℕ) : ℕ :=
  2 * n + 3 + d * ((n + c + 1) ^ d * (3 * (n + c) + 3) + 2) + ((n + c) ^ d + 1) +
    ((jsL k1).length + 1 + (n + ((n + c) ^ d + (n + c))) +
      ((n + c) ^ d + 1) * pushMax (prog k0 k1 M main c d s0))

theorem comp_run [Fintype Λ] [Fintype σ] [Fintype (Γ k0)] (w : List (Γ k0)) (O : List (Γ k1)) :
    ∃ L : List (Γ k1), ∃ t ≤ Bnd k0 k1 M main c d s0 w.length,
      (flip bind (TM2.step (prog k0 k1 M main c d s0)))^[t] (some (initList (compTM k0 k1 M main c d s0) w)) =
        some (haltList (compTM k0 k1 M main c d s0) L) ∧
      ((∃ t' ≤ (w.length + c) ^ d, ∃ c' : TM2.Cfg Γ Λ σ,
          (flip bind (TM2.step M))^[t' + 1] (some ⟨some main, s0, Function.update (fun k => ([] : List (Γ k))) k0 w⟩) =
            some c' ∧ c'.l = none ∧ c'.stk k1 = O) → L = O) := by
  have hI : initList (compTM k0 k1 M main c d s0) w =
      ⟨some (.inl (.inl none)), (s0, none), stkL (Function.update (fun k => ([] : List (Γ k))) k0 w)
        ![[], [], [], [], []]⟩ := by
    unfold initList
    congr 1
    funext j
    rcases j with k | a
    · by_cases h : k = k0
      · subst h
        exact (dif_pos rfl).trans (by rw [stkL_inl, Function.update_self]; rfl)
      · exact (dif_neg (show ¬ ((Sum.inl k : K ⊕ Fin 5) = Sum.inl k0) from
          fun e => h (Sum.inl_injective e))).trans (by rw [stkL_inl, Function.update_of_ne h]; rfl)
    · exact (dif_neg (show ¬ ((Sum.inr a : K ⊕ Fin 5) = Sum.inl k0) from Sum.inr_ne_inl)).trans
        (by fin_cases a <;> rfl)
  obtain ⟨t1, ht1, h1⟩ := init_run k0 k1 M main c d s0 s0 w
  set S0 := Function.update (fun k => ([] : List (Γ k))) k0 w with hS0
  set T0 : Fin 5 → List (Option (Γ k0)) := ![List.replicate ((w.length + c) ^ d) none,
    List.replicate w.length none ++ List.replicate c none, [], [], []] with hT0d
  have hM : ∀ l, prog k0 k1 M main c d s0 (.inr (.inl l)) =
      liftS (fun l => .inr (.inl l)) (.inr (.inr ⟨0, Nat.succ_pos _⟩)) (0 : Fin 5) (M l) := fun _ => rfl
  have hT0 : (T0 0).length = (w.length + c) ^ d := by simp [hT0d]
  have hS0s : ∑ k, (S0 k).length = w.length := by
    rw [Finset.sum_eq_single k0 (fun k _ hk => by simp [hS0, Function.update_of_ne hk]) (by simp)]
    simp [hS0]
  have htot0 : tot (stkL S0 T0) = w.length + ((w.length + c) ^ d + (w.length + c)) := by
    rw [tot_stkL, hS0s, Fin.sum_univ_five]
    simp [hT0d]
    try ring
  -- common tail: from the exit label
  have tail : ∀ (t' : ℕ) (cv : σ) (cs : ∀ k, List (Γ k)) (T' : Fin 5 → List (Option (Γ k0)))
      (b' : Option (Option (Γ k0))), t' ≤ (w.length + c) ^ d →
      (flip bind (TM2.step (prog k0 k1 M main c d s0)))^[t' + 1]
        (some ⟨some (.inr (.inl main)), (s0, none), stkL S0 T0⟩) =
        some ⟨some (.inr (.inr ⟨0, Nat.succ_pos _⟩)), (cv, b'), stkL cs T'⟩ →
      ∃ t ≤ Bnd k0 k1 M main c d s0 w.length,
        (flip bind (TM2.step (prog k0 k1 M main c d s0)))^[t] (some (initList (compTM k0 k1 M main c d s0) w)) =
          some (haltList (compTM k0 k1 M main c d s0) (cs k1)) := by
    intro t' cv cs T' b' ht' h2
    obtain ⟨t3, ht3, h3⟩ := exit_halt k0 k1 M main c d s0 (cv, b') (stkL cs T')
    have hgrow : tot (stkL cs T') ≤ tot (stkL S0 T0) + (t' + 1) * pushMax (prog k0 k1 M main c d s0) :=
      tot_iter _ _ _ _ h2
    have hmul : (t' + 1) * pushMax (prog k0 k1 M main c d s0) ≤
        ((w.length + c) ^ d + 1) * pushMax (prog k0 k1 M main c d s0) := Nat.mul_le_mul_right _ (by omega)
    refine ⟨t3 + ((t' + 1) + t1), ?_, ?_⟩
    · unfold Bnd
      omega
    · have key : (flip bind (TM2.step (prog k0 k1 M main c d s0)))^[t3 + ((t' + 1) + t1)]
          (some ⟨some (.inl (.inl none)), (s0, none), stkL S0 ![[], [], [], [], []]⟩) =
          some (haltList (compTM k0 k1 M main c d s0) (cs k1)) := by
        rw [Function.iterate_add_apply _ t3, Function.iterate_add_apply _ (t' + 1), h1, h2]
        exact h3
      rw [hI]
      exact key
  by_cases H : ∃ t' ≤ (w.length + c) ^ d, ∃ c' : TM2.Cfg Γ Λ σ,
      (flip bind (TM2.step M))^[t' + 1] (some ⟨some main, s0, S0⟩) = some c' ∧ c'.l = none ∧ c'.stk k1 = O
  · obtain ⟨t', ht', c', hc', hl, hO⟩ := H
    obtain ⟨T', b', h2⟩ := sim_halt M (prog k0 k1 M main c d s0) (fun l => .inr (.inl l))
      (.inr (.inr ⟨0, Nat.succ_pos _⟩)) (0 : Fin 5) hM t' ⟨some main, s0, S0⟩ c' T0 none hc' hl
      (by rw [hT0]; exact ht')
    obtain ⟨t, ht, h⟩ := tail t' c'.var c'.stk T' b' ht' h2
    exact ⟨c'.stk k1, t, ht, h, fun _ => hO⟩
  · obtain ⟨t', ht', c1, -, T', b', h2⟩ := reach_exit M (prog k0 k1 M main c d s0) (fun l => .inr (.inl l))
      (.inr (.inr ⟨0, Nat.succ_pos _⟩)) (0 : Fin 5) hM ((w.length + c) ^ d) T0 hT0 main s0 S0 none
    obtain ⟨t, ht, h⟩ := tail t' c1.var c1.stk T' b' ht' h2
    exact ⟨c1.stk k1, t, ht, h, fun h' => absurd h' H⟩

/-- a TM2 machine that is correct within `(|a| + c) ^ d` steps on the valid inputs gives a
polynomial-time computable function agreeing with `g` on them -/
theorem robust_polytime [Fintype Λ] [Fintype σ] [Fintype (Γ k0)] (e0 : Γ k0 ≃ Bool) (e1 : Γ k1 ≃ Bool)
    (V : List Bool → Prop) (g : List Bool → List Bool)
    (hV : ∀ a, V a → ∃ t' ≤ (a.length + c) ^ d, ∃ c' : TM2.Cfg Γ Λ σ,
      (flip bind (TM2.step M))^[t' + 1]
        (some ⟨some main, s0, Function.update (fun k => ([] : List (Γ k))) k0 (a.map e0.symm)⟩) =
        some c' ∧ c'.l = none ∧ c'.stk k1 = (g a).map e1.symm) :
    ∃ u : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) u) ∧
      ∀ a, V a → u a = g a := by
  have hex : ∀ a : List Bool, ∃ L : List (Γ k1), ∃ t ≤ Bnd k0 k1 M main c d s0 a.length,
      (flip bind (TM2.step (prog k0 k1 M main c d s0)))^[t]
        (some (initList (compTM k0 k1 M main c d s0) (a.map e0.symm))) =
        some (haltList (compTM k0 k1 M main c d s0) L) ∧ (V a → L = (g a).map e1.symm) := by
    intro a
    obtain ⟨L, t, ht, h, hL⟩ := comp_run k0 k1 M main c d s0 (a.map e0.symm) ((g a).map e1.symm)
    rw [List.length_map] at ht hL
    exact ⟨L, t, ht, h, fun hv => hL (hV a hv)⟩
  choose L t ht hrun hLV using hex
  let Q : Polynomial ℕ := 2 * Polynomial.X + 3 + Polynomial.C d * ((Polynomial.X + Polynomial.C (c + 1)) ^ d *
      (3 * (Polynomial.X + Polynomial.C c) + 3) + 2) + ((Polynomial.X + Polynomial.C c) ^ d + 1) +
    (Polynomial.C ((jsL k1).length + 1) + (Polynomial.X + ((Polynomial.X + Polynomial.C c) ^ d +
      (Polynomial.X + Polynomial.C c))) + ((Polynomial.X + Polynomial.C c) ^ d + 1) *
        Polynomial.C (pushMax (prog k0 k1 M main c d s0)))
  have hQ : ∀ n, Bnd k0 k1 M main c d s0 n ≤ Q.eval n := by
    intro n
    apply le_of_eq
    simp only [Q, Bnd, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_ofNat, Polynomial.eval_one]
    ring
  have hout : ∀ a, TM2OutputsInTime (compTM k0 k1 M main c d s0) (List.map e0.invFun (id a))
      (some (List.map e1.invFun (id ((L a).map e1)))) (Q.eval (id a).length) := by
    intro a
    have hm : List.map e1.invFun ((L a).map e1) = L a := by simp [List.map_map]
    unfold TM2OutputsInTime
    refine ⟨⟨t a, ?_⟩, (ht a).trans (hQ _)⟩
    have hr := hrun a
    rw [← hm] at hr
    exact hr
  refine ⟨fun a => (L a).map e1, ⟨{ tm := compTM k0 k1 M main c d s0, inputAlphabet := e0, outputAlphabet := e1, time := Q, outputsFun := hout }⟩, ?_⟩
  · intro a hv
    simp only [hLV a hv, List.map_map]
    simp

end Robust

end E261Clock

namespace E261Clock
open Turing

lemma step_halted {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} (M : Λ → TM2.Stmt Γ Λ σ)
    (c : TM2.Cfg Γ Λ σ) (hl : c.l = none) : TM2.step M c = none := by
  obtain ⟨l, v, S⟩ := c
  simp only at hl
  subst hl
  rfl

lemma after_halt {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} (M : Λ → TM2.Stmt Γ Λ σ)
    (s c : TM2.Cfg Γ Λ σ) (t : ℕ) (h : (flip bind (TM2.step M))^[t + 1] (some s) = some c)
    (hl : c.l = none) (k : ℕ) : (flip bind (TM2.step M))^[k + (t + 2)] (some s) = none := by
  rw [Function.iterate_add_apply, show t + 2 = (t + 1) + 1 from rfl, Function.iterate_succ_apply', h]
  show (flip bind (TM2.step M))^[k] (TM2.step M c) = none
  rw [step_halted M c hl]
  exact iter_none _ k

theorem halt_unique {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} (M : Λ → TM2.Stmt Γ Λ σ)
    (s : TM2.Cfg Γ Λ σ) (t1 t2 : ℕ) (c1 c2 : TM2.Cfg Γ Λ σ)
    (h1 : (flip bind (TM2.step M))^[t1 + 1] (some s) = some c1) (hl1 : c1.l = none)
    (h2 : (flip bind (TM2.step M))^[t2 + 1] (some s) = some c2) (hl2 : c2.l = none) : c1 = c2 := by
  rcases lt_trichotomy t1 t2 with h | h | h
  · have := after_halt M s c1 t1 h1 hl1 (t2 - t1 - 1)
    rw [show t2 - t1 - 1 + (t1 + 2) = t2 + 1 by omega, h2] at this
    exact absurd this (by simp)
  · subst h
    rw [h1] at h2
    exact Option.some_injective _ h2
  · have := after_halt M s c2 t2 h2 hl2 (t1 - t2 - 1)
    rw [show t1 - t2 - 1 + (t2 + 2) = t1 + 1 by omega, h1] at this
    exact absurd this (by simp)

theorem clocked {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} (k0 k1 : K) [Inhabited (Γ k0)]
    {Λ σ : Type} [Fintype Λ] [Fintype σ] [Fintype (Γ k0)] (M : Λ → TM2.Stmt Γ Λ σ) (main : Λ)
    (c d : ℕ) (s0 : σ) (e0 : Γ k0 ≃ Bool) (e1 : Γ k1 ≃ Bool) {I : Type} (inp out : I → List Bool)
    (h : ∀ i, ∃ t ≤ ((inp i).length + c) ^ d, ∃ cf : TM2.Cfg Γ Λ σ,
      (flip bind (TM2.step M))^[t + 1]
        (some ⟨some main, s0, Function.update (fun k => ([] : List (Γ k))) k0 ((inp i).map e0.symm)⟩) =
        some cf ∧ cf.l = none ∧ cf.stk k1 = (out i).map e1.symm) :
    ∃ u : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) u) ∧
      ∀ i, u (inp i) = out i := by
  classical
  let V : List Bool → Prop := fun a => ∃ i, inp i = a
  let g : List Bool → List Bool := fun a => if hv : V a then out hv.choose else []
  have hg : ∀ i, g (inp i) = out i := by
    intro i
    have hv : V (inp i) := ⟨i, rfl⟩
    show (if hv : V (inp i) then out hv.choose else []) = out i
    rw [dif_pos hv]
    obtain ⟨t1, -, c1, h1, hl1, hs1⟩ := h hv.choose
    obtain ⟨t2, -, c2, h2, hl2, hs2⟩ := h i
    rw [hv.choose_spec] at h1
    have := halt_unique M _ t1 t2 c1 c2 h1 hl1 h2 hl2
    subst this
    rw [hs1] at hs2
    exact List.map_injective_iff.mpr e1.symm.injective hs2
  obtain ⟨u, hu, hug⟩ := robust_polytime k0 k1 M main c d s0 e0 e1 V g (by
    rintro a ⟨i, rfl⟩
    rw [hg i]
    exact h i)
  exact ⟨u, hu, fun i => (hug _ ⟨i, rfl⟩).trans (hg i)⟩

end E261Clock

theorem solution {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} (k0 k1 : K) [Inhabited (Γ k0)]
    {Λ σ : Type} [Fintype Λ] [Fintype σ] [Fintype (Γ k0)] (M : Λ → Turing.TM2.Stmt Γ Λ σ) (main : Λ)
    (c d : ℕ) (s0 : σ) (e0 : Γ k0 ≃ Bool) (e1 : Γ k1 ≃ Bool) {I : Type} (inp out : I → List Bool)
    (h : ∀ i, ∃ t ≤ ((inp i).length + c) ^ d, ∃ cf : Turing.TM2.Cfg Γ Λ σ,
      (flip bind (Turing.TM2.step M))^[t + 1]
        (some ⟨some main, s0, Function.update (fun k => ([] : List (Γ k))) k0 ((inp i).map e0.symm)⟩) =
        some cf ∧ cf.l = none ∧ cf.stk k1 = (out i).map e1.symm) :
    ∃ u : List Bool → List Bool,
      Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) u) ∧
      ∀ i, u (inp i) = out i := by
  exact E261Clock.clocked k0 k1 M main c d s0 e0 e1 inp out h

#print axioms solution
