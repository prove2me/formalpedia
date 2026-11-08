-- Prove2me | solution 1 for TwoAgentSched.cpLoop_cost
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-07T12:57:58.314182+00:00
-- url     : https://prove2.me/submissions/b2f509b2-3a41-4b13-8597-8bfaaee1042f

import Mathlib
import Definitions.Def_TwoAgentSched_cpAlgo

open TwoAgentSched

namespace TwoAgentSched.CpLoopCost

@[simp] lemma cost_pure {α : Type} (a : α) : (pure a : Timed α).cost = 0 := rfl

@[simp] lemma cost_bind {α β : Type} (x : Timed α) (f : α → Timed β) :
    (x >>= f).cost = x.cost + (f x.val).cost := rfl

@[simp] lemma val_pure {α : Type} (a : α) : (pure a : Timed α).val = a := rfl

@[simp] lemma val_bind {α β : Type} (x : Timed α) (f : α → Timed β) :
    (x >>= f).val = (f x.val).val := rfl

@[simp] lemma cost_tick : tick.cost = 1 := rfl

@[simp] lemma cost_evalC {R S : Type} (f : R → S) (t : R) : (evalC f t).cost = 1 := rfl

@[simp] lemma cost_leC {α : Type} [LinearOrder α] (a b : α) : (leC a b).cost = 1 := rfl

@[simp] lemma cost_lookupC {ι S : Type} (D : ι → S) (k : ι) : (lookupC D k).cost = 1 := rfl

@[simp] lemma cost_subC {R : Type} [Sub R] (a b : R) : (subC a b).cost = 1 := rfl

@[simp] lemma cost_addC {R : Type} [Add R] (a b : R) : (addC a b).cost = 1 := rfl

@[simp] lemma cost_ticks (k : ℕ) : (ticks k).cost = k := rfl

@[simp] lemma val_tick : tick.val = () := rfl

@[simp] lemma val_evalC {R S : Type} (f : R → S) (t : R) : (evalC f t).val = f t := rfl

@[simp] lemma val_leC {α : Type} [LinearOrder α] (a b : α) :
    (leC a b).val = decide (a ≤ b) := rfl

@[simp] lemma val_lookupC {ι S : Type} (D : ι → S) (k : ι) : (lookupC D k).val = D k := rfl

@[simp] lemma val_subC {R : Type} [Sub R] (a b : R) : (subC a b).val = a - b := rfl

@[simp] lemma val_addC {R : Type} [Add R] (a b : R) : (addC a b).val = a + b := rfl

@[simp] lemma val_ticks (k : ℕ) : (ticks k).val = () := rfl

@[simp] lemma cost_ite_pure {α : Type} (c : Bool) (a b : α) :
    (if c then pure a else pure b : Timed α).cost = 0 := by
  cases c <;> rfl

@[simp] lemma cost_ite_pure_prop {α : Type} (p : Prop) [Decidable p] (a b : α) :
    (if p then pure a else pure b : Timed α).cost = 0 := by
  split <;> rfl

@[simp] lemma val_ite_pure {α : Type} (c : Bool) (a b : α) :
    (if c then pure a else pure b : Timed α).val = if c then a else b := by
  cases c <;> rfl

@[simp] lemma val_ite_pure_prop {α : Type} (p : Prop) [Decidable p] (a b : α) :
    (if p then pure a else pure b : Timed α).val = if p then a else b := by
  split <;> rfl

lemma argminC_cost_le {nA : ℕ} (fA : Fin nA → ℝ → ℝ) (τ : ℝ) :
    ∀ As : List (Fin nA), (argminC fA τ As).cost ≤ 3 * As.length := by
  intro As
  induction As with
  | nil => simp [argminC]
  | cons a as ih =>
      simp [argminC]
      split <;> simp_all <;> omega

lemma eraseC_cost_le {α : Type} [DecidableEq α] (x : α) :
    ∀ xs : List α, (eraseC x xs).cost ≤ xs.length := by
  intro xs
  induction xs with
  | nil => simp [eraseC]
  | cons y ys ih =>
      simp [eraseC]
      split <;> simp_all <;> omega

lemma argminC_mem {nA : ℕ} (fA : Fin nA → ℝ → ℝ) (τ : ℝ) :
    ∀ {As : List (Fin nA)} {h : Fin nA} {v : ℝ},
      (argminC fA τ As).val = some (h, v) → h ∈ As := by
  intro As
  induction As with
  | nil => simp [argminC]
  | cons a as ih =>
      intro h v hres
      rw [argminC] at hres
      simp only [val_bind, val_pure, val_tick, val_evalC] at hres
      split at hres
      · simp at hres
        obtain ⟨rfl, rfl⟩ := hres
        simp
      · rename_i h' v' heq
        simp only [val_bind, val_leC] at hres
        by_cases hle : decide (fA a τ ≤ v') = true
        · simp [hle] at hres
          obtain ⟨rfl, rfl⟩ := hres
          simp
        · simp [hle] at hres
          obtain ⟨rfl, rfl⟩ := hres
          exact List.mem_cons_of_mem a (ih heq)

lemma eraseC_length_of_mem {α : Type} [DecidableEq α] (x : α) :
    ∀ xs : List α, x ∈ xs → (eraseC x xs).val.length + 1 = xs.length := by
  intro xs
  induction xs with
  | nil => simp
  | cons y ys ih =>
      intro hx
      simp [eraseC]
      split
      · rename_i hy
        simp
      · rename_i hy
        have hx' : x ∈ ys := by
          simp only [List.mem_cons] at hx
          exact hx.resolve_left (by intro h; exact hy h.symm)
        have := ih hx'
        omega

lemma scanA_cost_le {nA : ℕ} (fA : Fin nA → ℝ → ℝ) (τ : ℝ) (As : List (Fin nA)) :
    (scanA fA τ As).cost ≤ 4 * As.length := by
  generalize hr : (argminC fA τ As).val = r
  cases r with
  | none =>
      rw [scanA]
      simp [hr]
      have := argminC_cost_le fA τ As
      omega
  | some hv =>
      obtain ⟨h, v⟩ := hv
      rw [scanA]
      simp [hr]
      have h1 := argminC_cost_le fA τ As
      have h2 := eraseC_cost_le h As
      omega

lemma scanA_cost_le_real {nA : ℕ} (fA : Fin nA → ℝ → ℝ) (τ : ℝ) (As : List (Fin nA)) :
    ((scanA fA τ As).cost : ℝ) ≤ 4 * (As.length : ℝ) := by
  exact_mod_cast scanA_cost_le fA τ As

lemma scanA_length {nA : ℕ} (fA : Fin nA → ℝ → ℝ) (τ : ℝ) :
    ∀ {As : List (Fin nA)} {h : Fin nA} {As' : List (Fin nA)},
      (scanA fA τ As).val = some (h, As') → As'.length + 1 = As.length := by
  intro As h As' hres
  rw [scanA] at hres
  generalize hr : (argminC fA τ As).val = r at hres
  cases r with
  | none => simp [hr] at hres
  | some hv =>
      obtain ⟨h0, v⟩ := hv
      simp [hr] at hres
      obtain ⟨rfl, rfl⟩ := hres
      have hmem : h0 ∈ As := argminC_mem fA τ hr
      exact eraseC_length_of_mem h0 As hmem

lemma scanA_length_real {nA : ℕ} (fA : Fin nA → ℝ → ℝ) (τ : ℝ) :
    ∀ {As : List (Fin nA)} {h : Fin nA} {As' : List (Fin nA)},
      (scanA fA τ As).val = some (h, As') → (As'.length : ℝ) + 1 = (As.length : ℝ) := by
  intro As h As' heq
  exact_mod_cast scanA_length fA τ heq

lemma cpLoop_cost_aux {nA nB : ℕ} (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ)
    (D : Fin nB → WithTop (ℝ ×ₗ Bool)) (fuel : ℕ) :
    ∀ (τ : ℝ) (As : List (Fin nA)) (Bs : List (Fin nB)) (acc : List (Job nA nB)),
      ((cpLoop p fA D fuel τ As Bs acc).cost : ℝ) ≤
        8 * ((As.length : ℝ) ^ 2 + (As.length : ℝ) + (Bs.length : ℝ) + 1) := by
  induction fuel with
  | zero =>
      intro τ As Bs acc
      simp [cpLoop]
      positivity
  | succ fuel ih =>
      intro τ As Bs acc
      cases Bs with
      | nil =>
          cases As with
          | nil => simp [cpLoop]
          | cons a as =>
              simp [cpLoop]
              split
              · simp
                have hscan := scanA_cost_le_real fA τ (a :: as)
                simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hscan
                nlinarith [show (0:ℝ) ≤ (as.length : ℝ) by positivity]
              · rename_i h As' heq
                simp
                have hscan := scanA_cost_le_real fA τ (a :: as)
                have hlen := scanA_length_real fA τ heq
                simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hscan hlen
                have hih := ih (τ - p (Sum.inl h)) As' [] (Sum.inl h :: acc)
                simp at hih
                nlinarith [show (0:ℝ) ≤ (As'.length : ℝ) by positivity, show (0:ℝ) ≤ (as.length : ℝ) by positivity]
      | cons k ks =>
          simp [cpLoop]
          by_cases hle : (↑(toLex (τ, true)) : WithTop (ℝ ×ₗ Bool)) ≤ D k
          · simp [hle]
            have hih := ih (τ - p (Sum.inr k)) As ks (Sum.inr k :: acc)
            nlinarith [show (0:ℝ) ≤ (As.length : ℝ) by positivity, show (0:ℝ) ≤ (ks.length : ℝ) by positivity]
          · simp [hle]
            cases As with
            | nil =>
                simp
                nlinarith [show (0:ℝ) ≤ (ks.length : ℝ) by positivity]
            | cons a as =>
                simp
                split
                · simp
                  have hscan := scanA_cost_le_real fA τ (a :: as)
                  simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hscan
                  nlinarith [show (0:ℝ) ≤ (as.length : ℝ) by positivity, show (0:ℝ) ≤ (ks.length : ℝ) by positivity]
                · rename_i h As' heq
                  simp
                  have hscan := scanA_cost_le_real fA τ (a :: as)
                  have hlen := scanA_length_real fA τ heq
                  simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hscan hlen
                  have hih := ih (τ - p (Sum.inl h)) As' (k :: ks) (Sum.inl h :: acc)
                  simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hih
                  nlinarith [show (0:ℝ) ≤ (As'.length : ℝ) by positivity, show (0:ℝ) ≤ (as.length : ℝ) by positivity,
                    show (0:ℝ) ≤ (ks.length : ℝ) by positivity]

end TwoAgentSched.CpLoopCost


open TwoAgentSched

/-- **The A-scan happens at most `n_A` times** (Agnetis–Mirchandani–Pacciarelli–Pacifici, Oper.
Res. 52(2) (2004), p. 233): there is one absolute constant `C` such that one A-scan costs at most
`C · |As|` and the main loop costs at most `C · (|As|² + |As| + |Bs| + 1)`. -/
theorem solution :
    ∃ C : ℝ,
      (∀ (nA : ℕ) (fA : Fin nA → ℝ → ℝ) (τ : ℝ) (As : List (Fin nA)),
        ((scanA fA τ As).cost : ℝ) ≤ C * (As.length : ℝ)) ∧
      ∀ (nA nB : ℕ) (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ)
        (D : Fin nB → WithTop (ℝ ×ₗ Bool)) (fuel : ℕ) (τ : ℝ) (As : List (Fin nA))
        (Bs : List (Fin nB)) (acc : List (Job nA nB)),
        ((cpLoop p fA D fuel τ As Bs acc).cost : ℝ) ≤
          C * ((As.length : ℝ) ^ 2 + (As.length : ℝ) + (Bs.length : ℝ) + 1) := by
  refine ⟨8, ?_, ?_⟩
  · intro nA fA τ As
    have h := TwoAgentSched.CpLoopCost.scanA_cost_le_real fA τ As
    nlinarith [h, show (0 : ℝ) ≤ (As.length : ℝ) by positivity]
  · intro nA nB p fA D fuel τ As Bs acc
    exact TwoAgentSched.CpLoopCost.cpLoop_cost_aux p fA D fuel τ As Bs acc
