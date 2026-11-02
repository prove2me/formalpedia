-- Prove2me | solution 1 for QuantumMaxCutEnergy.tm2_to_boolean_stacks
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T04:23:05.24972+00:00
-- url     : https://prove2.me/submissions/25584ed5-3e1b-4b35-84d4-3c1e9810c92e

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Mathlib
open scoped BigOperators

namespace QMCBoolSim
open Turing Function OAI.MetricKMedian.Binary

section Sim
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- Boolean statements over the extended state. -/
abbrev St (K Λ σ : Type) := TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)

/-- Push the first `n` bits of `g v`, so that bit `0` ends on top. -/
def pushAt (k : K) (g : σ × Option Bool → List Bool) : ℕ → St K Λ σ → St K Λ σ
  | 0, q => q
  | n + 1, q => .push k (fun v => (g v).getD n false) (pushAt k g n q)

theorem pushAt_spec (k : K) (g : σ × Option Bool → List Bool) (n : ℕ) (q : St K Λ σ)
    (v : σ × Option Bool) (s : K → List Bool) (hn : n ≤ (g v).length) :
    TM2.stepAux (pushAt k g n q) v s = TM2.stepAux q v (update s k ((g v).take n ++ s k)) := by
  induction n generalizing s with
  | zero => simp [pushAt]
  | succ n ih =>
      simp only [pushAt, TM2.stepAux]
      rw [ih _ (by omega)]
      have hlt : n < (g v).length := by omega
      simp only [update_self, update_idem]
      congr 2
      rw [List.getD_eq_getElem _ _ hlt, List.take_succ_eq_append_getElem hlt]
      simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- Read `n` bits from `k`, remembering them in the control flow. -/
def readTree (k : K) : ℕ → (List Bool → St K Λ σ) → St K Λ σ → St K Λ σ
  | 0, cont, _ => cont []
  | n + 1, cont, e =>
      .pop k (fun v x => (v.1, x))
        (.branch (fun v => v.2.isSome)
          (.branch (fun v => v.2 == some true)
            (readTree k n (fun l => cont (true :: l)) e)
            (readTree k n (fun l => cont (false :: l)) e))
          e)

theorem readTree_spec (k : K) (l : List Bool) (cont : List Bool → St K Λ σ) (e : St K Λ σ)
    (v : σ) (b : Option Bool) (s : K → List Bool) (rest : List Bool) (hs : s k = l ++ rest) :
    ∃ b', TM2.stepAux (readTree k l.length cont e) (v, b) s
      = TM2.stepAux (cont l) (v, b') (update s k rest) := by
  induction l generalizing cont b s with
  | nil =>
      refine ⟨b, ?_⟩
      have : update s k rest = s := by
        have : rest = s k := by simpa using hs.symm
        rw [this]; simp
      rw [this]; rfl
  | cons x l ih =>
      have hs' : s k = x :: (l ++ rest) := by simpa using hs
      cases x with
      | true =>
          obtain ⟨b', hb⟩ := ih (fun l => cont (true :: l)) (some true)
            (update s k (l ++ rest)) (by simp)
          refine ⟨b', ?_⟩
          simp only [update_idem] at hb
          simpa [List.length_cons, readTree, TM2.stepAux, hs'] using hb
      | false =>
          obtain ⟨b', hb⟩ := ih (fun l => cont (false :: l)) (some false)
            (update s k (l ++ rest)) (by simp)
          refine ⟨b', ?_⟩
          simp only [update_idem] at hb
          simpa [List.length_cons, readTree, TM2.stepAux, hs'] using hb

theorem readTree_empty (k : K) (n : ℕ) (cont : List Bool → St K Λ σ) (e : St K Λ σ)
    (v : σ) (b : Option Bool) (s : K → List Bool) (hs : s k = []) :
    TM2.stepAux (readTree k (n + 1) cont e) (v, b) s = TM2.stepAux e (v, none) s := by
  have : update s k [] = s := by rw [← hs]; simp
  simp [readTree, TM2.stepAux, hs, this]

/-- The symbols pushed by a statement. -/
def syms : TM2.Stmt Γ Λ σ → Set (Σ k, Γ k)
  | .push k f q => Set.range (fun v => (⟨k, f v⟩ : Σ k, Γ k)) ∪ syms q
  | .peek _ _ q => syms q
  | .pop _ _ q => syms q
  | .load _ q => syms q
  | .branch _ q r => syms q ∪ syms r
  | .goto _ => ∅
  | .halt => ∅

theorem syms_finite [Finite σ] (q : TM2.Stmt Γ Λ σ) : (syms q).Finite := by
  induction q with
  | push k f q ih => exact (Set.finite_range _).union ih
  | peek k f q ih => exact ih
  | pop k f q ih => exact ih
  | load f q ih => exact ih
  | branch f q r ihq ihr => exact ihq.union ihr
  | goto f => exact Set.finite_empty
  | halt => exact Set.finite_empty

variable (w : K → ℕ) (c : ∀ k, Γ k → List Bool) (d : ∀ k, List Bool → Option (Γ k))

/-- Translate a statement to Boolean stacks. -/
def tr : TM2.Stmt Γ Λ σ → St K Λ σ
  | .push k f q => pushAt k (fun v => c k (f v.1)) (w k) (tr q)
  | .peek k f q =>
      readTree k (w k)
        (fun l => pushAt k (fun _ => l) (w k) (.load (fun v => (f v.1 (d k l), none)) (tr q)))
        (.load (fun v => (f v.1 none, none)) (tr q))
  | .pop k f q =>
      readTree k (w k)
        (fun l => .load (fun v => (f v.1 (d k l), none)) (tr q))
        (.load (fun v => (f v.1 none, none)) (tr q))
  | .load f q => .load (fun v => (f v.1, none)) (tr q)
  | .branch f q r => .branch (fun v => f v.1) (tr q) (tr r)
  | .goto f => .goto (fun v => f v.1)
  | .halt => .halt

/-- Encode the stacks. -/
def enc (s : ∀ k, List (Γ k)) : K → List Bool := fun k => (s k).flatMap (c k)

/-- Encode a configuration. -/
def ecfg (a : TM2.Cfg Γ Λ σ) : TM2.Cfg (fun _ : K => Bool) Λ (σ × Option Bool) :=
  ⟨a.l, (a.var, none), enc c a.stk⟩

theorem enc_update (s : ∀ k, List (Γ k)) (k : K) (t : List (Γ k)) :
    enc c (update s k t) = update (enc c s) k (t.flatMap (c k)) := by
  funext j
  by_cases h : j = k
  · subst h; simp [enc]
  · simp [enc, update_of_ne h]

variable (T : Set (Σ k, Γ k))

theorem inv_update {s : ∀ k, List (Γ k)} (hs : ∀ k x, x ∈ s k → (⟨k, x⟩ : Σ k, Γ k) ∈ T)
    {k : K} {t : List (Γ k)} (ht : ∀ x ∈ t, (⟨k, x⟩ : Σ k, Γ k) ∈ T) :
    ∀ j x, x ∈ update s k t j → (⟨j, x⟩ : Σ k, Γ k) ∈ T := by
  intro j x hx
  by_cases h : j = k
  · subst h
    simp only [update_self] at hx
    exact ht x hx
  · rw [update_of_ne h] at hx
    exact hs j x hx

variable (hw : ∀ k, 0 < w k)
  (hlen : ∀ k x, (⟨k, x⟩ : Σ k, Γ k) ∈ T → (c k x).length = w k)
  (hd : ∀ k x, (⟨k, x⟩ : Σ k, Γ k) ∈ T → d k (c k x) = some x)

include hw hlen hd in
theorem tr_spec (q : TM2.Stmt Γ Λ σ) (hq : syms q ⊆ T) (v : σ) (s : ∀ k, List (Γ k))
    (hs : ∀ k x, x ∈ s k → (⟨k, x⟩ : Σ k, Γ k) ∈ T) :
    TM2.stepAux (tr w c d q) (v, none) (enc c s) = ecfg c (TM2.stepAux q v s) ∧
      (∀ k x, x ∈ (TM2.stepAux q v s).stk k → (⟨k, x⟩ : Σ k, Γ k) ∈ T) := by
  induction q generalizing v s with
  | push k f q ih =>
      have hfv : (⟨k, f v⟩ : Σ k, Γ k) ∈ T := hq (Or.inl ⟨v, rfl⟩)
      have hs' := inv_update T hs (k := k) (t := f v :: s k) (by
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hfv
        · exact hs k x hx)
      have ih' := ih (fun _ hx => hq (Or.inr hx)) v _ hs'
      simp only [tr, TM2.stepAux]
      refine ⟨?_, ih'.2⟩
      rw [pushAt_spec _ _ _ _ _ _ (by simp [hlen k _ hfv]), ← ih'.1, enc_update]
      congr 2
      rw [List.take_of_length_le (by simp [hlen k _ hfv])]
      simp [enc]
  | peek k f q ih =>
      have hq' : syms q ⊆ T := hq
      simp only [tr, TM2.stepAux]
      cases hsk : s k with
      | nil =>
          have ih' := ih hq' (f v none) s hs
          refine ⟨?_, ih'.2⟩
          obtain ⟨n, hn⟩ : ∃ n, w k = n + 1 := Nat.exists_eq_succ_of_ne_zero (hw k).ne'
          rw [hn, readTree_empty _ _ _ _ _ _ _ (by simp [enc, hsk])]
          simpa [TM2.stepAux] using ih'.1
      | cons x t =>
          have hx : (⟨k, x⟩ : Σ k, Γ k) ∈ T := hs k x (by simp [hsk])
          have ih' := ih hq' (f v (some x)) s hs
          refine ⟨?_, ih'.2⟩
          obtain ⟨b', hb⟩ := readTree_spec (Λ := Λ) k (c k x)
            (fun l => pushAt k (fun _ => l) (w k) (.load (fun v => (f v.1 (d k l), none))
              (tr w c d q)))
            (.load (fun v => (f v.1 none, none)) (tr w c d q)) v none (enc c s)
            (t.flatMap (c k)) (by simp [enc, hsk])
          rw [hlen k x hx] at hb
          simp only [List.head?_cons]
          rw [hb]
          rw [pushAt_spec _ _ _ _ _ _ (by simp [hlen k _ hx]),
            List.take_of_length_le (by simp [hlen k _ hx])]
          simp only [TM2.stepAux, hd k x hx, update_idem, update_self]
          have : update (enc c s) k (c k x ++ t.flatMap (c k)) = enc c s := by
            have : c k x ++ t.flatMap (c k) = enc c s k := by simp [enc, hsk]
            rw [this]; simp
          rw [this]
          exact ih'.1
  | pop k f q ih =>
      have hq' : syms q ⊆ T := hq
      simp only [tr, TM2.stepAux]
      cases hsk : s k with
      | nil =>
          have hup : update s k [] = s := by rw [← hsk]; simp
          have ih' := ih hq' (f v none) s hs
          simp only [List.tail_nil, List.head?_nil, hup]
          refine ⟨?_, ih'.2⟩
          obtain ⟨n, hn⟩ : ∃ n, w k = n + 1 := Nat.exists_eq_succ_of_ne_zero (hw k).ne'
          rw [hn, readTree_empty _ _ _ _ _ _ _ (by simp [enc, hsk])]
          simpa [TM2.stepAux] using ih'.1
      | cons x t =>
          have hx : (⟨k, x⟩ : Σ k, Γ k) ∈ T := hs k x (by simp [hsk])
          have hs' := inv_update T hs (k := k) (t := t) (by
            intro y hy
            exact hs k y (by simp [hsk, hy]))
          have ih' := ih hq' (f v (some x)) _ hs'
          simp only [List.tail_cons, List.head?_cons]
          refine ⟨?_, ih'.2⟩
          obtain ⟨b', hb⟩ := readTree_spec (Λ := Λ) k (c k x)
            (fun l => .load (fun v => (f v.1 (d k l), none)) (tr w c d q))
            (.load (fun v => (f v.1 none, none)) (tr w c d q)) v none (enc c s)
            (t.flatMap (c k)) (by simp [enc, hsk])
          rw [hlen k x hx] at hb
          rw [hb]
          simp only [TM2.stepAux, hd k x hx]
          rw [← enc_update]
          exact ih'.1
  | load f q ih =>
      have ih' := ih hq (f v) s hs
      simp only [tr, TM2.stepAux]
      exact ih'
  | branch f q r ihq ihr =>
      have hq' : syms q ⊆ T := fun _ hx => hq (Or.inl hx)
      have hr' : syms r ⊆ T := fun _ hx => hq (Or.inr hx)
      simp only [tr, TM2.stepAux]
      cases hf : f v with
      | false => simpa using ihr hr' v s hs
      | true => simpa using ihq hq' v s hs
  | goto f =>
      exact ⟨rfl, hs⟩
  | halt =>
      exact ⟨rfl, hs⟩

include hw hlen hd in
theorem sim_trace (m : Λ → TM2.Stmt Γ Λ σ) (hm : ∀ l, syms (m l) ⊆ T)
    {n : ℕ} {a b : TM2.Cfg Γ Λ σ} (h : Trace (TM2.step m) n a b)
    (ha : ∀ k x, x ∈ a.stk k → (⟨k, x⟩ : Σ k, Γ k) ∈ T) :
    Trace (TM2.step (fun l => tr w c d (m l))) n (ecfg c a) (ecfg c b) := by
  induction h with
  | refl => exact Trace.refl _
  | @cons n a b e hab _ ih =>
      rcases a with ⟨l, v, s⟩
      cases l with
      | none => cases hab
      | some l =>
          have hb : b = TM2.stepAux (m l) v s := (Option.some.inj hab).symm
          subst b
          have hspec := tr_spec w c d T hw hlen hd (m l) (hm l) v s ha
          refine Trace.cons ?_ (ih hspec.2)
          exact congrArg some hspec.1

end Sim

theorem exists_block (A : Type) (S : Set A) (hS : S.Finite) :
    ∃ (w : ℕ) (c : A → List Bool), 0 < w ∧ (∀ x ∈ S, (c x).length = w) ∧ Set.InjOn c S := by
  classical
  haveI : Finite S := hS
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin S
  let i : A → ℕ := fun x => if h : x ∈ S then (e ⟨x, h⟩).val else 0
  refine ⟨n + 1, fun x => List.ofFn (fun j : Fin (n + 1) => decide (j.val = i x)),
    Nat.succ_pos _, fun x _ => by simp, ?_⟩
  intro x hx y hy hxy
  have hxy' := List.ofFn_injective hxy
  have hix : i x < n + 1 := by
    have : i x = (e ⟨x, hx⟩).val := by simp [i, hx]
    have := (e ⟨x, hx⟩).isLt
    omega
  have h1 := congrFun hxy' ⟨i x, hix⟩
  simp only [decide_true] at h1
  have h2 : i x = i y := by simpa using h1.symm
  have h3 : e ⟨x, hx⟩ = e ⟨y, hy⟩ := by
    apply Fin.ext
    simpa [i, hx, hy] using h2
  simpa using e.injective h3

/-- The Boolean machine simulating a bundled machine. -/
abbrev simMachine (tm : FinTM2) (w : tm.K → ℕ) (c : ∀ k, tm.Γ k → List Bool)
    (d : ∀ k, List Bool → Option (tm.Γ k)) : Machine :=
  letI := tm.kDecidableEq
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  { K := tm.K
    input := tm.k₀
    output := tm.k₁
    Label := tm.Λ
    main := tm.main
    State := tm.σ × Option Bool
    initial := (tm.initialState, none)
    code := fun l => tr w c d (tm.m l) }

theorem simulate (tm : FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) :
    ∃ (M : Machine) (τ : Bool ≃ Bool), ∀ (s t : List Bool) (n : ℕ),
      TM2OutputsInTime tm (s.map e₀.symm) (some (t.map e₁.symm)) n →
        Nonempty (TM2OutputsInTime M.tm s (some (t.map τ)) n) := by
  classical
  letI := tm.kDecidableEq
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  let T : Set (Σ k, tm.Γ k) :=
    (⋃ l, syms (tm.m l)) ∪ Set.range (fun x : tm.Γ tm.k₀ => (⟨tm.k₀, x⟩ : Σ k, tm.Γ k))
  haveI : Finite (tm.Γ tm.k₀) := Finite.of_equiv Bool e₀.symm
  have hT : T.Finite :=
    (Set.finite_iUnion fun l => syms_finite (tm.m l)).union (Set.finite_range _)
  have key : ∀ k, ∃ (w : ℕ) (c : tm.Γ k → List Bool), 0 < w ∧
      (∀ x, (⟨k, x⟩ : Σ k, tm.Γ k) ∈ T → (c x).length = w) ∧
      (∀ x y, (⟨k, x⟩ : Σ k, tm.Γ k) ∈ T → (⟨k, y⟩ : Σ k, tm.Γ k) ∈ T → c x = c y → x = y) ∧
      (∀ h : k = tm.k₀, ∀ x, c x = [e₀ (h ▸ x)]) ∧
      (k ≠ tm.k₀ → ∀ h : k = tm.k₁, ∀ x, c x = [e₁ (h ▸ x)]) := by
    intro k
    by_cases h0 : k = tm.k₀
    · subst h0
      refine ⟨1, fun x => [e₀ x], one_pos, fun _ _ => rfl, ?_, fun _ _ => rfl, fun h => absurd rfl h⟩
      intro x y _ _ hxy
      exact e₀.injective (by simpa using hxy)
    · by_cases h1 : k = tm.k₁
      · subst h1
        refine ⟨1, fun x => [e₁ x], one_pos, fun _ _ => rfl, ?_, fun h => absurd h h0,
          fun _ _ _ => rfl⟩
        intro x y _ _ hxy
        exact e₁.injective (by simpa using hxy)
      · have hS : {x : tm.Γ k | (⟨k, x⟩ : Σ k, tm.Γ k) ∈ T}.Finite :=
          hT.preimage (f := fun x : tm.Γ k => (⟨k, x⟩ : Σ k, tm.Γ k))
            (sigma_mk_injective.injOn)
        obtain ⟨w, c, hw, hl, hi⟩ := exists_block _ _ hS
        exact ⟨w, c, hw, hl, fun x y hx hy h => hi hx hy h, fun h => absurd h h0,
          fun _ h => absurd h h1⟩
  choose w c hw hlen hinj hc0 hc1 using key
  let d : ∀ k, List Bool → Option (tm.Γ k) := fun k l =>
    if h : ∃ x, (⟨k, x⟩ : Σ k, tm.Γ k) ∈ T ∧ c k x = l then some h.choose else none
  have hd : ∀ k x, (⟨k, x⟩ : Σ k, tm.Γ k) ∈ T → d k (c k x) = some x := by
    intro k x hx
    have h : ∃ y, (⟨k, y⟩ : Σ k, tm.Γ k) ∈ T ∧ c k y = c k x := ⟨x, hx, rfl⟩
    have hspec := h.choose_spec
    simp only [d, dif_pos h]
    exact congrArg some (hinj k _ _ hspec.1 hx hspec.2)
  have hc0' : ∀ x, c tm.k₀ x = [e₀ x] := fun x => hc0 tm.k₀ rfl x
  obtain ⟨τ, hτ⟩ : ∃ τ : Bool ≃ Bool, ∀ x, c tm.k₁ x = [τ (e₁ x)] := by
    by_cases h : tm.k₁ = tm.k₀
    · have aux : ∀ k (_ : k = tm.k₀) (e : tm.Γ k ≃ Bool),
          ∃ τ : Bool ≃ Bool, ∀ x, c k x = [τ (e x)] := by
        intro k hk e
        subst hk
        exact ⟨e.symm.trans e₀, fun x => by simp [hc0']⟩
      exact aux _ h e₁
    · exact ⟨Equiv.refl _, fun x => hc1 tm.k₁ h rfl x⟩
  have hin : ∀ s : List Bool, (s.map e₀.symm).flatMap (c tm.k₀) = s := by
    intro s
    induction s with
    | nil => rfl
    | cons b s ih => simpa [hc0'] using ih
  have hout : ∀ t : List Bool, (t.map e₁.symm).flatMap (c tm.k₁) = t.map τ := by
    intro t
    induction t with
    | nil => rfl
    | cons b t ih => simpa [hτ] using ih
  refine ⟨simMachine tm w c d, τ, ?_⟩
  intro s t n h
  have htr : Trace (TM2.step tm.m) h.steps _ _ := Trace.of_iterate (f := tm.step) h.evals_in_steps
  have hsim := sim_trace w c d T hw hlen hd tm.m
    (fun l x hx => Or.inl (Set.mem_iUnion.2 ⟨l, hx⟩)) htr (by
      intro k x hx
      by_cases hk : k = tm.k₀
      · subst hk
        exact Or.inr ⟨_, rfl⟩
      · simp [initList, hk] at hx)
  have hinit : ecfg c (initList tm (s.map e₀.symm)) = (simMachine tm w c d).initialCfg s := by
    refine congrArg (TM2.Cfg.mk _ _) ?_
    funext k
    by_cases hk : k = tm.k₀
    · subst hk
      simpa [enc, initList, Machine.initialCfg] using hin s
    · simp [enc, initList, Machine.initialCfg, hk]
  have hhalt : ecfg c (haltList tm (t.map e₁.symm)) = (simMachine tm w c d).finalCfg (t.map τ) := by
    refine congrArg (TM2.Cfg.mk _ _) ?_
    funext k
    by_cases hk : k = tm.k₁
    · subst hk
      simpa [enc, haltList, Machine.finalCfg] using hout t
    · simp [enc, haltList, Machine.finalCfg, hk]
  rw [hinit, hhalt] at hsim
  exact ⟨⟨⟨_, hsim.iterate_eq⟩, h.steps_le_m⟩⟩

/-- A letterwise transducer. -/
def mapT (τ : Bool → Bool) : Transducer where
  Q := Unit
  initial := ()
  next _ b := ((), [τ b])
  finish _ := []

theorem mapT_run (τ : Bool → Bool) (xs : List Bool) : (mapT τ).run () xs = xs.map τ := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change τ b :: (mapT τ).run () xs = τ b :: xs.map τ; rw [ih]

end QMCBoolSim

theorem solution
    {α : Type} (ea : α → List Bool) (f : α → ℚ≥0)
    (h : Nonempty (Turing.TM2ComputableInPolyTime ea QuantumMaxCutEnergy.encodeValue f)) :
    Nonempty (OAI.MetricKMedian.Binary.PolyProgram ea QuantumMaxCutEnergy.encodeValue f) := by
  obtain ⟨H⟩ := h
  obtain ⟨M, τ, hM⟩ := QMCBoolSim.simulate H.tm H.inputAlphabet H.outputAlphabet
  let P : OAI.MetricKMedian.Binary.PolyProgram ea
      (fun b => (QuantumMaxCutEnergy.encodeValue b).map τ) f :=
    ⟨M, H.time, fun a => (hM _ _ _ (H.outputsFun a)).some⟩
  let Q : OAI.MetricKMedian.Binary.PolyProgram
      (fun b => (QuantumMaxCutEnergy.encodeValue b).map τ) QuantumMaxCutEnergy.encodeValue id :=
    (QMCBoolSim.mapT τ.symm).program.recode
      (fun b => (QuantumMaxCutEnergy.encodeValue b).map τ) (fun _ => rfl) (fun b => by
        change (QMCBoolSim.mapT τ.symm).run () _ = _
        rw [QMCBoolSim.mapT_run]
        simp)
  exact ⟨(P.comp Q).congr f (fun _ => rfl)⟩
