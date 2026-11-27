-- Prove2me | solution 1 for PalomarZF207.calc_not_provC_one
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T23:20:31.924332+00:00
-- url     : https://prove2.me/submissions/b8f4d0c1-06ca-4159-b529-0a0ea31d8567

import Definitions.Def_palomar_zf207_history
import Definitions.Def_palomar_zf207_zf
import Definitions.Def_palomar_zf207_calc

open PalomarZF207
open PalomarZF207History
open PalomarZF207Calc

namespace DevCalcSound

attribute [local instance] Classical.propDecidable

/-! ### 1. Calculus C unpairing, semantics, and derivability -/

def unpairAux : Nat → Nat → Nat → Nat × Nat
  | 0, s, n => (s - n, n)
  | fuel + 1, s, n =>
    if n ≤ s then (s - n, n) else unpairAux fuel (s + 1) (n - (s + 1))

def unpair (n : Nat) : Nat × Nat := unpairAux n 0 n

private theorem tri_step (s : Nat) : (s + 1) * (s + 1 + 1) / 2 = s * (s + 1) / 2 + (s + 1) := by
  have hmul : (s + 1) * (s + 1 + 1) = s * (s + 1) + 2 * (s + 1) := by
    have h1 : (s + 1) * (s + 1 + 1) = (s + 1) * s + (s + 1) * 2 := Nat.mul_add (s + 1) s 2
    have h2 : (s + 1) * s = s * (s + 1) := Nat.mul_comm (s + 1) s
    omega
  omega

private theorem unpairAux_spec : ∀ fuel s n,
    (∀ a b, n + s * (s + 1) / 2 = cantor a b → a + b ≥ s → a + b ≤ s + fuel →
      unpairAux fuel s n = (a, b))
  | 0, s, n, a, b, heq, hge, hle => by
    have hab : a + b = s := by omega
    have hns : n = b := by unfold cantor at heq; rw [hab] at heq; omega
    simp [unpairAux, hns, show s - b = a by omega]
  | fuel + 1, s, n, a, b, heq, hge, hle => by
    unfold unpairAux
    by_cases h : n ≤ s
    · have hab : a + b = s := by
        apply Classical.byContradiction
        intro hne
        have hgt : a + b ≥ s + 1 := by omega
        unfold cantor at heq
        have htri : (a + b) * (a + b + 1) / 2 ≥ (s + 1) * (s + 1 + 1) / 2 := by
          apply Nat.div_le_div_right
          exact Nat.mul_le_mul hgt (Nat.succ_le_succ hgt)
        have hstep := tri_step s
        omega
      have hnb : n = b := by unfold cantor at heq; rw [hab] at heq; omega
      rw [if_pos h, hnb, show s - b = a by omega]
    · rw [if_neg h]
      have hgt : a + b ≥ s + 1 := by
        apply Classical.byContradiction
        intro hlt
        have hab : a + b = s := by omega
        unfold cantor at heq; rw [hab] at heq; omega
      apply unpairAux_spec fuel (s + 1) (n - (s + 1)) a b _ hgt (by omega)
      have hstep := tri_step s
      omega

theorem cantor_ge_sum (a b : Nat) : a + b ≤ cantor a b := by
  unfold cantor
  cases h : a + b with
  | zero => omega
  | succ k =>
    have hmul : (k + 1) * (k + 1 + 1) ≥ 2 * (k + 1) := by
      have hle : 2 ≤ k + 1 + 1 := by omega
      have := Nat.mul_le_mul_left (k + 1) hle
      omega
    omega

theorem unpair_cantor (a b : Nat) : unpair (cantor a b) = (a, b) := by
  apply unpairAux_spec (cantor a b) 0 (cantor a b) a b
  · simp
  · omega
  · simpa using cantor_ge_sum a b

private theorem unpairAux_le : ∀ fuel s n, (unpairAux fuel s n).1 + (unpairAux fuel s n).2 ≤ s + n
  | 0, s, n => by simp [unpairAux]
  | fuel + 1, s, n => by
    unfold unpairAux
    split
    · simp
    · have ih := unpairAux_le fuel (s + 1) (n - (s + 1))
      omega

theorem unpair_le (n : Nat) : (unpair n).1 + (unpair n).2 ≤ n := by
  unfold unpair
  simpa using unpairAux_le n 0 n

def upd {V : Type} (env : Nat → V) (k : Nat) (v : V) : Nat → V :=
  fun i => if i = k then v else env i

def evalC {V : Type} (E : V → V → Prop) : (n : Nat) → (Nat → V) → Prop
  | 0, _ => True
  | n + 1, env =>
    have h1 : (unpair ((n + 1) / 4)).1 < n + 1 := by have := unpair_le ((n + 1) / 4); omega
    have h2 : (unpair ((n + 1) / 4)).2 < n + 1 := by have := unpair_le ((n + 1) / 4); omega
    match (n + 1) % 4 with
    | 0 => evalC E (unpair ((n + 1) / 4)).1 env → evalC E (unpair ((n + 1) / 4)).2 env
    | 1 => E (env (unpair ((n + 1) / 4)).1) (env (unpair ((n + 1) / 4)).2)
    | 2 => ∀ v : V, evalC E (unpair ((n + 1) / 4)).1 (upd env (unpair ((n + 1) / 4)).2 v)
    | _ => env (unpair ((n + 1) / 4)).1 = env (unpair ((n + 1) / 4)).2
termination_by n => n

private theorem evalC_Ic {V : Type} (E : V → V → Prop) (a b : Nat) (env : Nat → V) :
    evalC E (Ic a b) env ↔ (evalC E a env → evalC E b env) := by
  unfold Ic
  cases hc : cantor a b with
  | zero =>
    have ha0 : a = 0 := by have := cantor_ge_sum a b; omega
    have hb0 : b = 0 := by have := cantor_ge_sum a b; omega
    subst ha0; subst hb0
    simp [evalC]
  | succ k =>
    have hpos : 4 * (k + 1) = (4 * k + 3) + 1 := by omega
    rw [hpos]
    conv => lhs; unfold evalC
    have hdiv : (4 * k + 3 + 1) / 4 = cantor a b := by omega
    have hmod : (4 * k + 3 + 1) % 4 = 0 := by omega
    simp [hdiv, hmod, unpair_cantor]

private theorem evalC_Mc {V : Type} (E : V → V → Prop) (a b : Nat) (env : Nat → V) :
    evalC E (Mc a b) env ↔ E (env a) (env b) := by
  unfold Mc
  conv => lhs; unfold evalC
  have hdiv : (4 * cantor a b + 1) / 4 = cantor a b := by omega
  have hmod : (4 * cantor a b + 1) % 4 = 1 := by omega
  simp [hdiv, hmod, unpair_cantor]

private theorem evalC_Uc {V : Type} (E : V → V → Prop) (a B : Nat) (env : Nat → V) :
    evalC E (Uc a B) env ↔ ∀ v : V, evalC E B (upd env a v) := by
  unfold Uc
  have hpos : 4 * cantor B a + 2 = (4 * cantor B a + 1) + 1 := by omega
  rw [hpos]
  conv => lhs; unfold evalC
  have hdiv : (4 * cantor B a + 1 + 1) / 4 = cantor B a := by omega
  have hmod : (4 * cantor B a + 1 + 1) % 4 = 2 := by omega
  simp [hdiv, hmod, unpair_cantor]

private theorem evalC_Ec {V : Type} (E : V → V → Prop) (a b : Nat) (env : Nat → V) :
    evalC E (Ec a b) env ↔ env a = env b := by
  unfold Ec
  have hpos : 4 * cantor a b + 3 = (4 * cantor a b + 2) + 1 := by omega
  rw [hpos]
  conv => lhs; unfold evalC
  have hdiv : (4 * cantor a b + 2 + 1) / 4 = cantor a b := by omega
  have hmod : (4 * cantor a b + 2 + 1) % 4 = 3 := by omega
  simp [hdiv, hmod, unpair_cantor]

private theorem evalC_one {V : Type} (E : V → V → Prop) (env : Nat → V) :
    evalC E 1 env ↔ E (env 0) (env 0) := by
  have : (1 : Nat) = Mc 0 0 := rfl
  rw [this, evalC_Mc]

private theorem evalC_congr {V : Type} (E : V → V → Prop) :
    ∀ (n : Nat) (env₁ env₂ : Nat → V),
      (∀ i < n, env₁ i = env₂ i) → (evalC E n env₁ ↔ evalC E n env₂)
  | 0, _, _, _ => by simp [evalC]
  | n + 1, env₁, env₂, h => by
    have h1 : (unpair ((n + 1) / 4)).1 < n + 1 := by have := unpair_le ((n + 1) / 4); omega
    have h2 : (unpair ((n + 1) / 4)).2 < n + 1 := by have := unpair_le ((n + 1) / 4); omega
    conv => lhs; unfold evalC
    conv => rhs; unfold evalC
    dsimp only
    split
    · have ih1 := evalC_congr E (unpair ((n + 1) / 4)).1 env₁ env₂ (fun i hi => h i (Nat.lt_trans hi h1))
      have ih2 := evalC_congr E (unpair ((n + 1) / 4)).2 env₁ env₂ (fun i hi => h i (Nat.lt_trans hi h2))
      rw [ih1, ih2]
    · rw [h _ h1, h _ h2]
    · constructor
      · intro hv v
        exact (evalC_congr E (unpair ((n + 1) / 4)).1 (upd env₁ (unpair ((n + 1) / 4)).2 v)
          (upd env₂ (unpair ((n + 1) / 4)).2 v) (fun i hi => by
            unfold upd; split
            · rfl
            · exact h i (Nat.lt_trans hi h1))).mp (hv v)
      · intro hv v
        exact (evalC_congr E (unpair ((n + 1) / 4)).1 (upd env₁ (unpair ((n + 1) / 4)).2 v)
          (upd env₂ (unpair ((n + 1) / 4)).2 v) (fun i hi => by
            unfold upd; split
            · rfl
            · exact h i (Nat.lt_trans hi h1))).mpr (hv v)
    · rw [h _ h1, h _ h2]
termination_by n => n

/-! ### 2. Compiling calculus C codes to `Formula` -/

private def bindVar (k : Nat) (i : Nat) : Nat := if i = k then 0 else i + 1

private def fTrue : Formula := .imp .bot .bot

private def codeToFormula : Nat → Formula
  | 0 => fTrue
  | n + 1 =>
    have h1 : (unpair ((n + 1) / 4)).1 < n + 1 := by have := unpair_le ((n + 1) / 4); omega
    have h2 : (unpair ((n + 1) / 4)).2 < n + 1 := by have := unpair_le ((n + 1) / 4); omega
    match (n + 1) % 4 with
    | 0 => .imp (codeToFormula (unpair ((n + 1) / 4)).1) (codeToFormula (unpair ((n + 1) / 4)).2)
    | 1 => .mem (unpair ((n + 1) / 4)).1 (unpair ((n + 1) / 4)).2
    | 2 => .all (rename (bindVar (unpair ((n + 1) / 4)).2) (codeToFormula (unpair ((n + 1) / 4)).1))
    | _ => .eq (unpair ((n + 1) / 4)).1 (unpair ((n + 1) / 4)).2
termination_by n => n

private theorem bound_mono : ∀ (f : Formula) {m n : Nat}, Bound f m → m ≤ n → Bound f n
  | .bot, _, _, _, _ => trivial
  | .mem _ _, _, _, ⟨h1, h2⟩, hle => ⟨Nat.lt_of_lt_of_le h1 hle, Nat.lt_of_lt_of_le h2 hle⟩
  | .eq _ _, _, _, ⟨h1, h2⟩, hle => ⟨Nat.lt_of_lt_of_le h1 hle, Nat.lt_of_lt_of_le h2 hle⟩
  | .and a b, _, _, ⟨h1, h2⟩, hle => ⟨bound_mono a h1 hle, bound_mono b h2 hle⟩
  | .or a b, _, _, ⟨h1, h2⟩, hle => ⟨bound_mono a h1 hle, bound_mono b h2 hle⟩
  | .imp a b, _, _, ⟨h1, h2⟩, hle => ⟨bound_mono a h1 hle, bound_mono b h2 hle⟩
  | .all a, _, _, h1, hle => bound_mono a h1 (Nat.succ_le_succ hle)
  | .ex a, _, _, h1, hle => bound_mono a h1 (Nat.succ_le_succ hle)

private theorem bound_rename :
    ∀ (f : Formula) (m n : Nat) (σ : Nat → Nat),
      Bound f m → (∀ i < m, σ i < n) → Bound (rename σ f) n
  | .bot, _, _, _, _, _ => trivial
  | .mem i j, _, _, _, ⟨hi, hj⟩, h => ⟨h i hi, h j hj⟩
  | .eq i j, _, _, _, ⟨hi, hj⟩, h => ⟨h i hi, h j hj⟩
  | .and a b, m, n, σ, ⟨ha, hb⟩, h =>
    ⟨bound_rename a m n σ ha h, bound_rename b m n σ hb h⟩
  | .or a b, m, n, σ, ⟨ha, hb⟩, h =>
    ⟨bound_rename a m n σ ha h, bound_rename b m n σ hb h⟩
  | .imp a b, m, n, σ, ⟨ha, hb⟩, h =>
    ⟨bound_rename a m n σ ha h, bound_rename b m n σ hb h⟩
  | .all a, m, n, σ, ha, h => by
    apply bound_rename a (m + 1) (n + 1) (lift σ) ha
    intro i hi
    cases i with
    | zero => exact Nat.zero_lt_succ n
    | succ k => exact Nat.succ_lt_succ (h k (Nat.lt_of_succ_lt_succ hi))
  | .ex a, m, n, σ, ha, h => by
    apply bound_rename a (m + 1) (n + 1) (lift σ) ha
    intro i hi
    cases i with
    | zero => exact Nat.zero_lt_succ n
    | succ k => exact Nat.succ_lt_succ (h k (Nat.lt_of_succ_lt_succ hi))

private theorem pushValue_comp_lift {V : Type} (σ : Nat → Nat) (s : Nat → V) (x : V) :
    (fun i => pushValue s x (lift σ i)) = pushValue (fun i => s (σ i)) x := by
  funext i; cases i <;> rfl

private theorem eval_rename {V : Type} (E : V → V → Prop) :
    ∀ (f : Formula) (σ : Nat → Nat) (s : Nat → V),
      eval E (rename σ f) s ↔ eval E f (fun i => s (σ i))
  | .bot, _, _ => Iff.rfl
  | .mem _ _, _, _ => Iff.rfl
  | .eq _ _, _, _ => Iff.rfl
  | .and p q, σ, s => by simp only [rename, eval, eval_rename E p σ s, eval_rename E q σ s]
  | .or p q, σ, s => by simp only [rename, eval, eval_rename E p σ s, eval_rename E q σ s]
  | .imp p q, σ, s => by simp only [rename, eval, eval_rename E p σ s, eval_rename E q σ s]
  | .all p, σ, s => by
    constructor
    · intro h x; have hx := (eval_rename E p (lift σ) (pushValue s x)).mp (h x); rwa [pushValue_comp_lift] at hx
    · intro h x; apply (eval_rename E p (lift σ) (pushValue s x)).mpr; rw [pushValue_comp_lift]; exact h x
  | .ex p, σ, s => by
    constructor
    · rintro ⟨x, hx⟩; have hx' := (eval_rename E p (lift σ) (pushValue s x)).mp hx; rw [pushValue_comp_lift] at hx'; exact ⟨x, hx'⟩
    · rintro ⟨x, hx⟩; refine ⟨x, (eval_rename E p (lift σ) (pushValue s x)).mpr ?_⟩; rw [pushValue_comp_lift]; exact hx

private theorem bound_codeToFormula : ∀ n : Nat, Bound (codeToFormula n) n
  | 0 => by simp [codeToFormula, fTrue, Bound]
  | n + 1 => by
    have h1 : (unpair ((n + 1) / 4)).1 < n + 1 := by have := unpair_le ((n + 1) / 4); omega
    have h2 : (unpair ((n + 1) / 4)).2 < n + 1 := by have := unpair_le ((n + 1) / 4); omega
    unfold codeToFormula
    dsimp only
    split
    · exact ⟨bound_mono _ (bound_codeToFormula (unpair ((n + 1) / 4)).1) (Nat.le_of_lt h1),
        bound_mono _ (bound_codeToFormula (unpair ((n + 1) / 4)).2) (Nat.le_of_lt h2)⟩
    · exact ⟨h1, h2⟩
    · apply bound_rename (codeToFormula (unpair ((n + 1) / 4)).1) (unpair ((n + 1) / 4)).1 (n + 1 + 1)
        (bindVar (unpair ((n + 1) / 4)).2) (bound_codeToFormula (unpair ((n + 1) / 4)).1)
      intro i hi
      unfold bindVar
      split <;> omega
    · exact ⟨h1, h2⟩
termination_by n => n

private theorem eval_codeToFormula {V : Type} (E : V → V → Prop) :
    ∀ (n : Nat) (env : Nat → V), eval E (codeToFormula n) env ↔ evalC E n env
  | 0, _ => by simp [codeToFormula, fTrue, eval, evalC]
  | n + 1, env => by
    have h1 : (unpair ((n + 1) / 4)).1 < n + 1 := by have := unpair_le ((n + 1) / 4); omega
    have h2 : (unpair ((n + 1) / 4)).2 < n + 1 := by have := unpair_le ((n + 1) / 4); omega
    conv => lhs; unfold codeToFormula
    conv => rhs; unfold evalC
    dsimp only
    split
    · simp only [eval]
      rw [eval_codeToFormula E (unpair ((n + 1) / 4)).1 env,
          eval_codeToFormula E (unpair ((n + 1) / 4)).2 env]
    · exact Iff.rfl
    · constructor
      · intro h v
        have hv := (eval_rename E (codeToFormula (unpair ((n + 1) / 4)).1)
          (bindVar (unpair ((n + 1) / 4)).2) (pushValue env v)).mp (h v)
        have hfn : (fun i => pushValue env v (bindVar (unpair ((n + 1) / 4)).2 i)) =
            upd env (unpair ((n + 1) / 4)).2 v := by
          funext i; unfold bindVar upd; split <;> rfl
        rw [hfn, eval_codeToFormula E (unpair ((n + 1) / 4)).1] at hv
        exact hv
      · intro h v
        apply (eval_rename E (codeToFormula (unpair ((n + 1) / 4)).1)
          (bindVar (unpair ((n + 1) / 4)).2) (pushValue env v)).mpr
        have hfn : (fun i => pushValue env v (bindVar (unpair ((n + 1) / 4)).2 i)) =
            upd env (unpair ((n + 1) / 4)).2 v := by
          funext i; unfold bindVar upd; split <;> rfl
        rw [hfn, eval_codeToFormula E (unpair ((n + 1) / 4)).1]
        exact h v
    · exact Iff.rfl
termination_by n => n

/-! ### 3. ZF Model Utilities (Extensionality, Separation, Replacement, Basic Sets) -/

private def pushParams {V : Type} (s : Nat → V) : List V → Nat → V
  | [] => s
  | x :: xs => pushParams (pushValue s x) xs

private theorem pushParams_append {V : Type} :
    ∀ (xs ys : List V) (s : Nat → V), pushParams s (xs ++ ys) = pushParams (pushParams s xs) ys
  | [], _, _ => rfl
  | x :: xs, ys, s => pushParams_append xs ys (pushValue s x)

private theorem eval_allPrefix {V : Type} (E : V → V → Prop) :
    ∀ (n : Nat) (f : Formula) (s : Nat → V) (ps : List V),
      ps.length = n → eval E (allPrefix n f) s → eval E f (pushParams s ps)
  | 0, _, _, [], _, h => h
  | n + 1, f, s, x :: xs, hlen, h =>
    eval_allPrefix E n f (pushValue s x) xs (Nat.succ.inj hlen) (h x)

private theorem eval_congr_bound {V : Type} (E : V → V → Prop) :
    ∀ (f : Formula) (n : Nat) (s₁ s₂ : Nat → V),
      Bound f n → (∀ i < n, s₁ i = s₂ i) → (eval E f s₁ ↔ eval E f s₂)
  | .bot, _, _, _, _, _ => Iff.rfl
  | .mem i j, _, _, _, ⟨hi, hj⟩, h => by simp [eval, h i hi, h j hj]
  | .eq i j, _, _, _, ⟨hi, hj⟩, h => by simp [eval, h i hi, h j hj]
  | .and a b, n, s₁, s₂, ⟨ha, hb⟩, h => by
    simp [eval, eval_congr_bound E a n s₁ s₂ ha h, eval_congr_bound E b n s₁ s₂ hb h]
  | .or a b, n, s₁, s₂, ⟨ha, hb⟩, h => by
    simp [eval, eval_congr_bound E a n s₁ s₂ ha h, eval_congr_bound E b n s₁ s₂ hb h]
  | .imp a b, n, s₁, s₂, ⟨ha, hb⟩, h => by
    simp [eval, eval_congr_bound E a n s₁ s₂ ha h, eval_congr_bound E b n s₁ s₂ hb h]
  | .all a, n, s₁, s₂, ha, h => by
    constructor
    · intro h1 x
      exact (eval_congr_bound E a (n + 1) (pushValue s₁ x) (pushValue s₂ x) ha (fun i hi => by
        cases i with | zero => rfl | succ k => exact h k (Nat.lt_of_succ_lt_succ hi))).mp (h1 x)
    · intro h2 x
      exact (eval_congr_bound E a (n + 1) (pushValue s₁ x) (pushValue s₂ x) ha (fun i hi => by
        cases i with | zero => rfl | succ k => exact h k (Nat.lt_of_succ_lt_succ hi))).mpr (h2 x)
  | .ex a, n, s₁, s₂, ha, h => by
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, (eval_congr_bound E a (n + 1) (pushValue s₁ x) (pushValue s₂ x) ha (fun i hi => by
        cases i with | zero => rfl | succ k => exact h k (Nat.lt_of_succ_lt_succ hi))).mp hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, (eval_congr_bound E a (n + 1) (pushValue s₁ x) (pushValue s₂ x) ha (fun i hi => by
        cases i with | zero => rfl | succ k => exact h k (Nat.lt_of_succ_lt_succ hi))).mpr hx⟩

section ZFModel

variable {V : Type} {E : V → V → Prop}

private noncomputable def arbV [Nonempty V] : V := Classical.choice inferInstance

private theorem ax_ext (hM : Model E) [Nonempty V] {a b : V}
    (h : ∀ x, E x a ↔ E x b) : a = b := by
  have s0 : Nat → V := fun _ => arbV
  have hAx : Axiom fixedExt := Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  exact hM fixedExt hAx s0 a b (fun x hx => (h x).mp hx) (fun x hx => (h x).mpr hx)

private theorem ax_empty (hM : Model E) [Nonempty V] : ∃ z : V, Empty E z := by
  have s0 : Nat → V := fun _ => arbV
  have hAx : Axiom fixedEmpty := Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  exact hM fixedEmpty hAx s0

private theorem ax_pair (hM : Model E) [Nonempty V] (a b : V) : ∃ p : V, Pair E a b p := by
  have s0 : Nat → V := fun _ => arbV
  have hAx : Axiom fixedPair :=
    Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  obtain ⟨p, hp⟩ := hM fixedPair hAx s0 a b
  exact ⟨p, fun x => ⟨(hp x).1, (hp x).2⟩⟩

private theorem ax_union (hM : Model E) [Nonempty V] (a : V) :
    ∃ u : V, ∀ x, E x u ↔ ∃ y, E y a ∧ E x y := by
  have s0 : Nat → V := fun _ => arbV
  have hAx : Axiom fixedUnion :=
    Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  obtain ⟨u, hu⟩ := hM fixedUnion hAx s0 a
  exact ⟨u, fun x => ⟨(hu x).1, (hu x).2⟩⟩

private theorem ax_power (hM : Model E) [Nonempty V] (a : V) :
    ∃ p : V, ∀ x, E x p ↔ ∀ y, E y x → E y a := by
  have s0 : Nat → V := fun _ => arbV
  have hAx : Axiom fixedPower :=
    Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  obtain ⟨p, hp⟩ := hM fixedPower hAx s0 a
  exact ⟨p, fun x => ⟨(hp x).1, (hp x).2⟩⟩

private theorem ax_omega (hM : Model E) [Nonempty V] : ∃ w : V, Omega E w := by
  have s0 : Nat → V := fun _ => arbV
  have hAx : Axiom fixedOmega :=
    Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  obtain ⟨w, ⟨⟨z, hz, hzw⟩, hstep⟩, hmin⟩ := hM fixedOmega hAx s0
  refine ⟨w, ⟨⟨z, hz, hzw⟩, fun x hx => ?_⟩, fun a ha x hx => ?_⟩
  · obtain ⟨y, hy, hyw⟩ := hstep x hx
    exact ⟨y, fun u => ⟨(hy u).1, (hy u).2⟩, hyw⟩
  · apply hmin a _ x hx
    exact ⟨ha.1, fun u hu => let ⟨v, hv, hva⟩ := ha.2 u hu; ⟨v, fun t => ⟨(hv t).mp, (hv t).mpr⟩, hva⟩⟩

private theorem ax_found (hM : Model E) [Nonempty V] {a : V} (hne : ∃ x, E x a) :
    ∃ x, E x a ∧ ∀ y, E y x → ¬ E y a := by
  have s0 : Nat → V := fun _ => arbV
  have hAx : Axiom fixedFoundation :=
    Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))))
  exact hM fixedFoundation hAx s0 a hne

private theorem ax_sep (hM : Model E) [Nonempty V]
    (n : Nat) (body : Formula) (hbd : Bound body (n + 1)) (ps : List V) (hlen : ps.length = n) (A : V) :
    ∃ B : V, ∀ x, E x B ↔ E x A ∧ eval E body (pushValue (pushParams (fun _ => arbV) ps) x) := by
  let s0 : Nat → V := fun _ => arbV
  have hAx : Axiom (separationSchema n body) := Or.inr (Or.inl ⟨n, body, hbd, rfl⟩)
  have hSep := eval_allPrefix E n (separationFormula (rename sepIndex body)) s0 ps hlen
    (hM _ hAx s0)
  obtain ⟨B, hB⟩ := hSep A
  refine ⟨B, fun x => ?_⟩
  have hbx := hB x
  have hren : eval E (rename sepIndex body) (pushValue (pushValue (pushValue (pushParams s0 ps) A) B) x) ↔
      eval E body (pushValue (pushParams s0 ps) x) := by
    rw [eval_rename]
    have hfn : (fun i => pushValue (pushValue (pushValue (pushParams s0 ps) A) B) x (sepIndex i)) =
        pushValue (pushParams s0 ps) x := by
      funext i
      cases i with
      | zero => rfl
      | succ k => simp [sepIndex, pushValue]
    rw [hfn]
  exact ⟨fun hx => let ⟨h1, h2⟩ := hbx.1 hx; ⟨h1, hren.mp h2⟩,
         fun ⟨h1, h2⟩ => hbx.2 ⟨h1, hren.mpr h2⟩⟩

private theorem ax_rep (hM : Model E) [Nonempty V]
    (n : Nat) (body : Formula) (hbd : Bound body (n + 2)) (ps : List V) (hlen : ps.length = n)
    (hFunc : ∀ x y₁ y₂,
      eval E body (pushValue (pushValue (pushParams (fun _ => arbV) ps) y₁) x) →
      eval E body (pushValue (pushValue (pushParams (fun _ => arbV) ps) y₂) x) →
      y₁ = y₂)
    (A : V) :
    ∃ B : V, ∀ y, E y B ↔
      ∃ x, E x A ∧ eval E body (pushValue (pushValue (pushParams (fun _ => arbV) ps) y) x) := by
  let s0 : Nat → V := fun _ => arbV
  have hAx : Axiom (replacementSchema n body) := Or.inr (Or.inr ⟨n, body, hbd, rfl⟩)
  have hRep := eval_allPrefix E n
    (replacementFormula (rename repAIndex body) (rename repBIndex body) (rename repCIndex body))
    s0 ps hlen (hM _ hAx s0)
  have hF : eval E (functionalityFormula (rename repAIndex body) (rename repBIndex body)) (pushParams s0 ps) := by
    intro x y₁ y₂ h1 h2
    rw [eval_rename] at h1 h2
    have hfn1 : (fun i => pushValue (pushValue (pushValue (pushParams s0 ps) x) y₁) y₂ (repAIndex i)) =
        pushValue (pushValue (pushParams s0 ps) y₁) x := by
      funext i; cases i with
      | zero => rfl
      | succ k => cases k with | zero => rfl | succ j => rfl
    have hfn2 : (fun i => pushValue (pushValue (pushValue (pushParams s0 ps) x) y₁) y₂ (repBIndex i)) =
        pushValue (pushValue (pushParams s0 ps) y₂) x := by
      funext i; cases i with
      | zero => rfl
      | succ k => cases k with | zero => rfl | succ j => rfl
    rw [hfn1] at h1; rw [hfn2] at h2
    exact hFunc x y₁ y₂ h1 h2
  obtain ⟨B, hB⟩ := hRep hF A
  refine ⟨B, fun y => ?_⟩
  have hby := hB y
  constructor
  · intro hy
    obtain ⟨x, hxA, hbody⟩ := hby.1 hy
    rw [eval_rename] at hbody
    have hfn : (fun i => pushValue (pushValue (pushValue (pushValue (pushParams s0 ps) A) B) y) x (repCIndex i)) =
        pushValue (pushValue (pushParams s0 ps) y) x := by
      funext i; cases i with
      | zero => rfl
      | succ k => cases k with | zero => rfl | succ j => rfl
    rw [hfn] at hbody
    exact ⟨x, hxA, hbody⟩
  · rintro ⟨x, hxA, hbody⟩
    apply hby.2
    refine ⟨x, hxA, ?_⟩
    rw [eval_rename]
    have hfn : (fun i => pushValue (pushValue (pushValue (pushValue (pushParams s0 ps) A) B) y) x (repCIndex i)) =
        pushValue (pushValue (pushParams s0 ps) y) x := by
      funext i; cases i with
      | zero => rfl
      | succ k => cases k with | zero => rfl | succ j => rfl
    rwa [hfn]

/-! ### 4. Formula combinators for Scott's trick -/

private def fNot (p : Formula) : Formula := .imp p .bot
private def fIff (p q : Formula) : Formula := .and (.imp p q) (.imp q p)

private def fEmpty (a : Nat) : Formula := .all (fNot (.mem 0 (a + 1)))
private def fSucc (a b : Nat) : Formula :=
  .all (fIff (.mem 0 (b + 1)) (.or (.mem 0 (a + 1)) (.eq 0 (a + 1))))
private def fPair (a b p : Nat) : Formula :=
  .all (fIff (.mem 0 (p + 1)) (.or (.eq 0 (a + 1)) (.eq 0 (b + 1))))
private def fOrderedPair (a b p : Nat) : Formula :=
  .ex (.ex (.and (fPair (a + 2) (a + 2) 1)
    (.and (fPair (a + 2) (b + 2) 0) (fPair 1 0 (p + 2)))))
private def fAt (f x y : Nat) : Formula :=
  .ex (.and (.mem 0 (f + 1)) (fOrderedPair (x + 1) (y + 1) 0))
private def fFunctionOn (f dom : Nat) : Formula :=
  .and
    (.all (.imp (.mem 0 (dom + 1))
      (.ex (.and (fAt (f + 2) 1 0) (.all (.imp (fAt (f + 3) 2 0) (.eq 0 1)))))))
    (.all (.imp (.mem 0 (f + 1))
      (.ex (.ex (.and (.mem 1 (dom + 3)) (fOrderedPair 1 0 2))))))
private def fSub (a b : Nat) : Formula := .all (.imp (.mem 0 (a + 1)) (.mem 0 (b + 1)))
private def fTrans (a : Nat) : Formula := .all (.imp (.mem 0 (a + 1)) (fSub 0 (a + 1)))
private def fOrdinal (a : Nat) : Formula := .and (fTrans a) (.all (.imp (.mem 0 (a + 1)) (fTrans 0)))

private def fVStage (f α : Nat) : Formula :=
  .and (fOrdinal α) (.and (fFunctionOn f α)
    (.all (.imp (.mem 0 (α + 1))
      (.all (.imp (fAt (f + 2) 1 0)
        (.all (fIff (.mem 0 1)
          (.ex (.and (.mem 0 3) (.ex (.and (fAt (f + 5) 1 0) (fSub 2 0))))))))))))

private def fVVal (α v : Nat) : Formula :=
  .ex (.ex (.and (fSucc (α + 2) 1) (.and (fVStage 0 1) (fAt 0 (α + 2) (v + 2)))))

private theorem bound_fEmpty {a n : Nat} (ha : a < n) : Bound (fEmpty a) n :=
  ⟨⟨Nat.zero_lt_succ n, Nat.succ_lt_succ ha⟩, trivial⟩

private theorem eval_fEmpty (a : Nat) (s : Nat → V) : eval E (fEmpty a) s ↔ Empty E (s a) := Iff.rfl

private theorem bound_fSucc {a b n : Nat} (ha : a < n) (hb : b < n) : Bound (fSucc a b) n :=
  ⟨⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩⟩,
   ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ⟨by omega, by omega⟩⟩⟩

private theorem eval_fSucc (a b : Nat) (s : Nat → V) : eval E (fSucc a b) s ↔ Succ E (s a) (s b) := by
  constructor
  · intro h x; exact ⟨(h x).1, (h x).2⟩
  · intro h x; exact ⟨(h x).mp, (h x).mpr⟩

private theorem bound_fPair {a b p n : Nat} (ha : a < n) (hb : b < n) (hp : p < n) : Bound (fPair a b p) n :=
  ⟨⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩⟩,
   ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ⟨by omega, by omega⟩⟩⟩

private theorem eval_fPair (a b p : Nat) (s : Nat → V) : eval E (fPair a b p) s ↔ Pair E (s a) (s b) (s p) := by
  constructor
  · intro h x; exact ⟨(h x).1, (h x).2⟩
  · intro h x; exact ⟨(h x).mp, (h x).mpr⟩

private theorem bound_fOrderedPair {a b p n : Nat} (ha : a < n) (hb : b < n) (hp : p < n) :
    Bound (fOrderedPair a b p) n :=
  ⟨bound_fPair (by omega) (by omega) (by omega),
   ⟨bound_fPair (by omega) (by omega) (by omega), bound_fPair (by omega) (by omega) (by omega)⟩⟩

private theorem eval_fOrderedPair (a b p : Nat) (s : Nat → V) :
    eval E (fOrderedPair a b p) s ↔ OrderedPair E (s a) (s b) (s p) := by
  constructor
  · rintro ⟨aa, ab, h1, h2, h3⟩
    exact ⟨aa, ab, (eval_fPair _ _ _ _).mp h1, (eval_fPair _ _ _ _).mp h2, (eval_fPair _ _ _ _).mp h3⟩
  · rintro ⟨aa, ab, h1, h2, h3⟩
    exact ⟨aa, ab, (eval_fPair _ _ _ _).mpr h1, (eval_fPair _ _ _ _).mpr h2, (eval_fPair _ _ _ _).mpr h3⟩

private theorem bound_fAt {f x y n : Nat} (hf : f < n) (hx : x < n) (hy : y < n) : Bound (fAt f x y) n :=
  ⟨⟨by omega, by omega⟩, bound_fOrderedPair (by omega) (by omega) (by omega)⟩

private theorem eval_fAt (f x y : Nat) (s : Nat → V) : eval E (fAt f x y) s ↔ At E (s f) (s x) (s y) := by
  constructor
  · rintro ⟨p, h1, h2⟩; exact ⟨p, h1, (eval_fOrderedPair _ _ _ _).mp h2⟩
  · rintro ⟨p, h1, h2⟩; exact ⟨p, h1, (eval_fOrderedPair _ _ _ _).mpr h2⟩

private theorem bound_fFunctionOn {f d n : Nat} (hf : f < n) (hd : d < n) : Bound (fFunctionOn f d) n :=
  ⟨⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega),
    ⟨bound_fAt (by omega) (by omega) (by omega), ⟨by omega, by omega⟩⟩⟩⟩,
   ⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, bound_fOrderedPair (by omega) (by omega) (by omega)⟩⟩⟩

private theorem eval_fFunctionOn (f d : Nat) (s : Nat → V) :
    eval E (fFunctionOn f d) s ↔ FunctionOn E (s f) (s d) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, fun p hp => ?_⟩
    · obtain ⟨y, hy, hu⟩ := h1 x hx
      exact ⟨y, (eval_fAt _ _ _ _).mp hy, fun z hz => hu z ((eval_fAt _ _ _ _).mpr hz)⟩
    · obtain ⟨x, y, hx, hp'⟩ := h2 p hp
      exact ⟨x, y, hx, (eval_fOrderedPair _ _ _ _).mp hp'⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, fun p hp => ?_⟩
    · obtain ⟨y, hy, hu⟩ := h1 x hx
      exact ⟨y, (eval_fAt _ _ _ _).mpr hy, fun z hz => hu z ((eval_fAt _ _ _ _).mp hz)⟩
    · obtain ⟨x, y, hx, hp'⟩ := h2 p hp
      exact ⟨x, y, hx, (eval_fOrderedPair _ _ _ _).mpr hp'⟩

private def SubSet (E : V → V → Prop) (a b : V) : Prop := ∀ x, E x a → E x b
private def TransSet (E : V → V → Prop) (a : V) : Prop := ∀ x, E x a → SubSet E x a
private def Ordinal (E : V → V → Prop) (a : V) : Prop := TransSet E a ∧ ∀ x, E x a → TransSet E x

private def VStage (E : V → V → Prop) (f α : V) : Prop :=
  Ordinal E α ∧ FunctionOn E f α ∧
  ∀ β, E β α → ∀ v, At E f β v →
    ∀ y, E y v ↔ ∃ γ, E γ β ∧ ∃ w, At E f γ w ∧ SubSet E y w

private def VVal (E : V → V → Prop) (α v : V) : Prop :=
  ∃ α' f, Succ E α α' ∧ VStage E f α' ∧ At E f α v

private theorem bound_fSub {a b n : Nat} (ha : a < n) (hb : b < n) : Bound (fSub a b) n :=
  ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

private theorem eval_fSub (a b : Nat) (s : Nat → V) : eval E (fSub a b) s ↔ SubSet E (s a) (s b) := Iff.rfl

private theorem bound_fTrans {a n : Nat} (ha : a < n) : Bound (fTrans a) n :=
  ⟨⟨by omega, by omega⟩, bound_fSub (by omega) (by omega)⟩

private theorem eval_fTrans (a : Nat) (s : Nat → V) : eval E (fTrans a) s ↔ TransSet E (s a) := Iff.rfl

private theorem bound_fOrdinal {a n : Nat} (ha : a < n) : Bound (fOrdinal a) n :=
  ⟨bound_fTrans ha, ⟨⟨by omega, by omega⟩, bound_fTrans (by omega)⟩⟩

private theorem eval_fOrdinal (a : Nat) (s : Nat → V) : eval E (fOrdinal a) s ↔ Ordinal E (s a) := Iff.rfl

private theorem bound_fVStage {f α n : Nat} (hf : f < n) (hα : α < n) : Bound (fVStage f α) n :=
  ⟨bound_fOrdinal hα, bound_fFunctionOn hf hα,
   ⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega),
    ⟨⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega), bound_fSub (by omega) (by omega)⟩⟩⟩,
     ⟨⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega), bound_fSub (by omega) (by omega)⟩⟩, ⟨by omega, by omega⟩⟩⟩⟩⟩⟩

private theorem eval_fVStage (f α : Nat) (s : Nat → V) : eval E (fVStage f α) s ↔ VStage E (s f) (s α) := by
  constructor
  · rintro ⟨ho, hfun, hstep⟩
    refine ⟨ho, (eval_fFunctionOn _ _ _).mp hfun, fun β hβ v hv y => ?_⟩
    have hy := hstep β hβ v ((eval_fAt _ _ _ _).mpr hv) y
    exact ⟨fun h => let ⟨γ, hγ, w, hw, hsub⟩ := hy.1 h; ⟨γ, hγ, w, (eval_fAt _ _ _ _).mp hw, hsub⟩,
           fun ⟨γ, hγ, w, hw, hsub⟩ => hy.2 ⟨γ, hγ, w, (eval_fAt _ _ _ _).mpr hw, hsub⟩⟩
  · rintro ⟨ho, hfun, hstep⟩
    refine ⟨ho, (eval_fFunctionOn _ _ _).mpr hfun, fun β hβ v hv y => ?_⟩
    have hy := hstep β hβ v ((eval_fAt _ _ _ _).mp hv) y
    exact ⟨fun h => let ⟨γ, hγ, w, hw, hsub⟩ := hy.mp h; ⟨γ, hγ, w, (eval_fAt _ _ _ _).mpr hw, hsub⟩,
           fun ⟨γ, hγ, w, hw, hsub⟩ => hy.mpr ⟨γ, hγ, w, (eval_fAt _ _ _ _).mp hw, hsub⟩⟩

private theorem bound_fVVal {α v n : Nat} (hα : α < n) (hv : v < n) : Bound (fVVal α v) n :=
  ⟨bound_fSucc (by omega) (by omega), ⟨bound_fVStage (by omega) (by omega), bound_fAt (by omega) (by omega) (by omega)⟩⟩

private theorem eval_fVVal (α v : Nat) (s : Nat → V) : eval E (fVVal α v) s ↔ VVal E (s α) (s v) := by
  constructor
  · rintro ⟨α', f, hs, hvs, hat⟩
    exact ⟨α', f, (eval_fSucc _ _ _).mp hs, (eval_fVStage _ _ _).mp hvs, (eval_fAt _ _ _ _).mp hat⟩
  · rintro ⟨α', f, hs, hvs, hat⟩
    exact ⟨α', f, (eval_fSucc _ _ _).mpr hs, (eval_fVStage _ _ _).mpr hvs, (eval_fAt _ _ _ _).mpr hat⟩

/-! ### 5. Set Theory in `(V, E)`: Ordinals, Cumulative Hierarchy `V_α`, Transitive Closure, Scott's Trick -/

private theorem pair_unique (hM : Model E) [Nonempty V] {a b p₁ p₂ : V}
    (h1 : Pair E a b p₁) (h2 : Pair E a b p₂) : p₁ = p₂ :=
  ax_ext hM (fun x => (h1 x).trans (h2 x).symm)

private theorem orderedPair_inj (hM : Model E) [Nonempty V] {a₁ b₁ a₂ b₂ p : V}
    (h1 : OrderedPair E a₁ b₁ p) (h2 : OrderedPair E a₂ b₂ p) : a₁ = a₂ ∧ b₁ = b₂ := by
  rcases h1 with ⟨aa₁, ab₁, haa₁, hab₁, hp₁⟩
  rcases h2 with ⟨aa₂, ab₂, haa₂, hab₂, hp₂⟩
  have hmem1 : aa₁ = aa₂ ∨ aa₁ = ab₂ := (hp₂ aa₁).mp ((hp₁ aa₁).mpr (Or.inl rfl))
  have ha12 : a₁ = a₂ := by
    cases hmem1 with
    | inl h =>
      have : E a₁ aa₂ := by rw [← h]; exact (haa₁ a₁).mpr (Or.inl rfl)
      cases (haa₂ a₁).mp this with | inl h' => exact h' | inr h' => exact h'
    | inr h =>
      have : E a₂ aa₁ := by rw [h]; exact (hab₂ a₂).mpr (Or.inl rfl)
      cases (haa₁ a₂).mp this with | inl h' => exact h'.symm | inr h' => exact h'.symm
  subst ha12
  have haaeq : aa₁ = aa₂ := pair_unique hM haa₁ haa₂
  subst haaeq
  refine ⟨rfl, ?_⟩
  by_cases hba : b₁ = a₁
  · subst hba
    have heq : ab₁ = aa₁ := pair_unique hM hab₁ haa₁
    have hmem2 : ab₂ = aa₁ ∨ ab₂ = ab₁ := (hp₁ ab₂).mp ((hp₂ ab₂).mpr (Or.inr rfl))
    have hab2 : ab₂ = aa₁ := by cases hmem2 with | inl h => exact h | inr h => exact h.trans heq
    have hb2 : E b₂ aa₁ := by rw [← hab2]; exact (hab₂ b₂).mpr (Or.inr rfl)
    cases (haa₁ b₂).mp hb2 with | inl h => exact h.symm | inr h => exact h.symm
  · have hne : ab₁ ≠ aa₁ := by
      intro heq
      have hb1 : E b₁ aa₁ := by rw [← heq]; exact (hab₁ b₁).mpr (Or.inr rfl)
      cases (haa₁ b₁).mp hb1 with | inl h => exact hba h | inr h => exact hba h
    have hmem2 : ab₁ = aa₁ ∨ ab₁ = ab₂ := (hp₂ ab₁).mp ((hp₁ ab₁).mpr (Or.inr rfl))
    have habeq : ab₁ = ab₂ := by cases hmem2 with | inl h => exact absurd h hne | inr h => exact h
    have hb1 : E b₁ ab₂ := by rw [← habeq]; exact (hab₁ b₁).mpr (Or.inr rfl)
    cases (hab₂ b₁).mp hb1 with | inl h => exact absurd h hba | inr h => exact h

private theorem orderedPair_exists (hM : Model E) [Nonempty V] (a b : V) :
    ∃ p, OrderedPair E a b p := by
  obtain ⟨aa, haa⟩ := ax_pair hM a a
  obtain ⟨ab, hab⟩ := ax_pair hM a b
  obtain ⟨p, hp⟩ := ax_pair hM aa ab
  exact ⟨p, aa, ab, haa, hab, hp⟩

private theorem binUnion_exists (hM : Model E) [Nonempty V] (a b : V) :
    ∃ u, ∀ x, E x u ↔ E x a ∨ E x b := by
  obtain ⟨p, hp⟩ := ax_pair hM a b
  obtain ⟨u, hu⟩ := ax_union hM p
  refine ⟨u, fun x => ?_⟩
  rw [hu]
  constructor
  · rintro ⟨y, hy, hxy⟩
    cases (hp y).mp hy with | inl h => subst h; exact Or.inl hxy | inr h => subst h; exact Or.inr hxy
  · intro h
    cases h with
    | inl h => exact ⟨a, (hp a).mpr (Or.inl rfl), h⟩
    | inr h => exact ⟨b, (hp b).mpr (Or.inr rfl), h⟩

private theorem succ_exists (hM : Model E) [Nonempty V] (a : V) : ∃ b, Succ E a b := by
  obtain ⟨sa, hsa⟩ := ax_pair hM a a
  obtain ⟨b, hb⟩ := binUnion_exists hM a sa
  refine ⟨b, fun x => ?_⟩
  rw [hb, hsa]
  exact ⟨fun h => by rcases h with h | h | h; exact Or.inl h; exact Or.inr h; exact Or.inr h,
         fun h => by rcases h with h | h; exact Or.inl h; exact Or.inr (Or.inl h)⟩

private theorem mem_irrefl (hM : Model E) [Nonempty V] (x : V) : ¬ E x x := by
  intro hxx
  obtain ⟨sx, hsx⟩ := ax_pair hM x x
  obtain ⟨m, hm, hmin⟩ := ax_found hM ⟨x, (hsx x).mpr (Or.inl rfl)⟩
  have hmx : m = x := by cases (hsx m).mp hm with | inl h => exact h | inr h => exact h
  subst hmx
  exact hmin m hxx hm

private theorem mem_asymm (hM : Model E) [Nonempty V] {x y : V} (hxy : E x y) (hyx : E y x) : False := by
  obtain ⟨p, hp⟩ := ax_pair hM x y
  obtain ⟨m, hm, hmin⟩ := ax_found hM ⟨x, (hp x).mpr (Or.inl rfl)⟩
  cases (hp m).mp hm with
  | inl h => subst h; exact hmin y hyx ((hp y).mpr (Or.inr rfl))
  | inr h => subst h; exact hmin x hxy ((hp x).mpr (Or.inl rfl))

private theorem ordinal_elem {α x : V} (hα : Ordinal E α) (hx : E x α) : Ordinal E x :=
  ⟨hα.2 x hx, fun y hy => hα.2 y (hα.1 x hx y hy)⟩

private theorem ordinal_succ {α α' : V} (hα : Ordinal E α) (hs : Succ E α α') : Ordinal E α' := by
  constructor
  · intro x hx y hy
    apply (hs y).mpr
    cases (hs x).mp hx with
    | inl hxα => exact Or.inl (hα.1 x hxα y hy)
    | inr hxeq => subst hxeq; exact Or.inl hy
  · intro x hx
    cases (hs x).mp hx with
    | inl hxα => exact hα.2 x hxα
    | inr hxeq => subst hxeq; exact hα.1

private theorem ordinal_union (_hM : Model E) [Nonempty V] {A U : V}
    (hOrd : ∀ x, E x A → Ordinal E x) (hU : ∀ y, E y U ↔ ∃ x, E x A ∧ E y x) :
    Ordinal E U := by
  constructor
  · intro x hx y hy
    obtain ⟨a, ha, hxa⟩ := (hU x).mp hx
    exact (hU y).mpr ⟨a, ha, (hOrd a ha).1 x hxa y hy⟩
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := (hU x).mp hx
    exact (hOrd a ha).2 x hxa

private theorem ordinal_empty {z : V} (hz : Empty E z) : Ordinal E z :=
  ⟨fun _ hx => False.elim (hz _ hx), fun _ hx => False.elim (hz _ hx)⟩

private theorem ordinal_trichotomy (hM : Model E) [Nonempty V] {α β : V}
    (hα : Ordinal E α) (hβ : Ordinal E β) : E α β ∨ α = β ∨ E β α := by
  obtain ⟨α', hα'⟩ := succ_exists hM α
  obtain ⟨β', hβ'⟩ := succ_exists hM β
  -- Bad(x) := ∃ y ∈ β', ¬ (x ∈ y ∨ x = y ∨ y ∈ x)
  let fBad : Formula := .ex (.and (.mem 0 2) (fNot (.or (.mem 1 0) (.or (.eq 1 0) (.mem 0 1)))))
  have hBadBd : Bound fBad 2 :=
    ⟨⟨by omega, by omega⟩, ⟨⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩⟩, trivial⟩⟩
  obtain ⟨B1, hB1⟩ := ax_sep hM 1 fBad hBadBd [β'] rfl α'
  by_cases hB1ne : ∃ x, E x B1
  · obtain ⟨x, hxB1, hminX⟩ := ax_found hM hB1ne
    obtain ⟨hxα', y0, hy0β', hnot0⟩ := (hB1 x).mp hxB1
    let fBadY : Formula := fNot (.or (.mem 1 0) (.or (.eq 1 0) (.mem 0 1)))
    have hBadYBd : Bound fBadY 2 :=
      ⟨⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩⟩, trivial⟩
    obtain ⟨B2, hB2⟩ := ax_sep hM 1 fBadY hBadYBd [x] rfl β'
    obtain ⟨y, hyB2, hminY⟩ := ax_found hM ⟨y0, (hB2 y0).mpr ⟨hy0β', hnot0⟩⟩
    obtain ⟨hyβ', hnotXY⟩ := (hB2 y).mp hyB2
    have hxOrd : Ordinal E x := ordinal_elem (ordinal_succ hα hα') hxα'
    have hyOrd : Ordinal E y := ordinal_elem (ordinal_succ hβ hβ') hyβ'
    have hxy : x = y := by
      apply ax_ext hM
      intro z
      constructor
      · intro hzx
        have hzα' : E z α' := (ordinal_succ hα hα').1 x hxα' z hzx
        have htri : E z y ∨ z = y ∨ E y z := by
          apply Classical.byContradiction
          intro hnot
          exact hminX z hzx ((hB1 z).mpr ⟨hzα', y, hyβ', hnot⟩)
        rcases htri with h1 | rfl | h3
        · exact h1
        · exact False.elim (hnotXY (Or.inr (Or.inr hzx)))
        · exact False.elim (hnotXY (Or.inr (Or.inr (hxOrd.1 z hzx y h3))))
      · intro hzy
        have hzβ' : E z β' := (ordinal_succ hβ hβ').1 y hyβ' z hzy
        have htri : E x z ∨ x = z ∨ E z x := by
          apply Classical.byContradiction
          intro hnot
          exact hminY z hzy ((hB2 z).mpr ⟨hzβ', hnot⟩)
        rcases htri with h1 | rfl | h3
        · exact False.elim (hnotXY (Or.inl (hyOrd.1 z hzy x h1)))
        · exact False.elim (hnotXY (Or.inl hzy))
        · exact h3
    exact False.elim (hnotXY (Or.inr (Or.inl hxy)))
  · apply Classical.byContradiction
    intro hnot
    exact hB1ne ⟨α, (hB1 α).mpr ⟨(hα' α).mpr (Or.inr rfl), β, (hβ' β).mpr (Or.inr rfl), hnot⟩⟩

/-! ### 6. Cumulative Hierarchy `VStage` Existence, Uniqueness, Monotonicity, Exhaustion -/

private theorem vstage_agree (hM : Model E) [Nonempty V] {f₁ f₂ α₁ α₂ : V}
    (h1 : VStage E f₁ α₁) (h2 : VStage E f₂ α₂) :
    ∀ γ, E γ α₁ → E γ α₂ → ∀ v₁ v₂, At E f₁ γ v₁ → At E f₂ γ v₂ → v₁ = v₂ := by
  -- Bad(γ) := γ ∈ α₁ ∧ γ ∈ α₂ ∧ ∃ v₁ v₂, At f₁ γ v₁ ∧ At f₂ γ v₂ ∧ v₁ ≠ v₂
  let fDiff : Formula :=
    .and (.mem 0 3) (.ex (.ex (.and (fAt 3 2 1) (.and (fAt 4 2 0) (fNot (.eq 1 0))))))
  have hDiffBd : Bound fDiff 4 :=
    ⟨⟨by omega, by omega⟩, bound_fAt (by omega) (by omega) (by omega),
     bound_fAt (by omega) (by omega) (by omega), ⟨⟨by omega, by omega⟩, trivial⟩⟩
  obtain ⟨D, hD⟩ := ax_sep hM 3 fDiff hDiffBd [α₂, f₂, f₁] rfl α₁
  intro γ hγα₁ hγα₂ v₁ v₂ hv₁ hv₂
  apply Classical.byContradiction
  intro hne
  have hDne : ∃ x, E x D := by
    refine ⟨γ, (hD γ).mpr ⟨hγα₁, hγα₂, v₁, v₂, ?_, ?_, hne⟩⟩
    · exact (eval_fAt _ _ _ _).mpr hv₁
    · exact (eval_fAt _ _ _ _).mpr hv₂
  obtain ⟨m, hmD, hmin⟩ := ax_found hM hDne
  obtain ⟨hmα₁, hmα₂, w₁, w₂, hw₁', hw₂', hwne⟩ := (hD m).mp hmD
  have hw₁ : At E f₁ m w₁ := (eval_fAt _ _ _ _).mp hw₁'
  have hw₂ : At E f₂ m w₂ := (eval_fAt _ _ _ _).mp hw₂'
  apply hwne
  change w₁ = w₂
  apply ax_ext hM
  intro y
  rw [h1.2.2 m hmα₁ w₁ hw₁ y, h2.2.2 m hmα₂ w₂ hw₂ y]
  constructor
  · rintro ⟨δ, hδm, u₁, hu₁, hsub⟩
    have hδα₁ : E δ α₁ := h1.1.1 m hmα₁ δ hδm
    have hδα₂ : E δ α₂ := h2.1.1 m hmα₂ δ hδm
    obtain ⟨u₂, hu₂, _⟩ := h2.2.1.1 δ hδα₂
    have hequ : u₁ = u₂ := by
      apply Classical.byContradiction
      intro hneu
      exact hmin δ hδm ((hD δ).mpr ⟨hδα₁, hδα₂, u₁, u₂,
        (eval_fAt _ _ _ _).mpr hu₁, (eval_fAt _ _ _ _).mpr hu₂, hneu⟩)
    subst hequ
    exact ⟨δ, hδm, u₁, hu₂, hsub⟩
  · rintro ⟨δ, hδm, u₂, hu₂, hsub⟩
    have hδα₁ : E δ α₁ := h1.1.1 m hmα₁ δ hδm
    have hδα₂ : E δ α₂ := h2.1.1 m hmα₂ δ hδm
    obtain ⟨u₁, hu₁, _⟩ := h1.2.1.1 δ hδα₁
    have hequ : u₁ = u₂ := by
      apply Classical.byContradiction
      intro hneu
      exact hmin δ hδm ((hD δ).mpr ⟨hδα₁, hδα₂, u₁, u₂,
        (eval_fAt _ _ _ _).mpr hu₁, (eval_fAt _ _ _ _).mpr hu₂, hneu⟩)
    subst hequ
    exact ⟨δ, hδm, u₁, hu₁, hsub⟩

private theorem vstage_unique (hM : Model E) [Nonempty V] {f₁ f₂ α : V}
    (h1 : VStage E f₁ α) (h2 : VStage E f₂ α) : f₁ = f₂ := by
  apply ax_ext hM
  intro p
  constructor
  · intro hp
    obtain ⟨x, y, hx, hpair⟩ := h1.2.1.2 p hp
    obtain ⟨y₂, hy₂, _⟩ := h2.2.1.1 x hx
    have heq : y = y₂ := vstage_agree hM h1 h2 x hx hx y y₂ ⟨p, hp, hpair⟩ hy₂
    subst heq
    obtain ⟨p₂, hp₂, hpair₂⟩ := hy₂
    have hpeq : p = p₂ := by
      rcases hpair with ⟨aa₁, ab₁, haa₁, hab₁, hpp₁⟩
      rcases hpair₂ with ⟨aa₂, ab₂, haa₂, hab₂, hpp₂⟩
      have haa : aa₁ = aa₂ := pair_unique hM haa₁ haa₂
      have hab : ab₁ = ab₂ := pair_unique hM hab₁ hab₂
      subst haa; subst hab
      exact pair_unique hM hpp₁ hpp₂
    rwa [hpeq]
  · intro hp
    obtain ⟨x, y, hx, hpair⟩ := h2.2.1.2 p hp
    obtain ⟨y₁, hy₁, _⟩ := h1.2.1.1 x hx
    have heq : y₁ = y := vstage_agree hM h1 h2 x hx hx y₁ y hy₁ ⟨p, hp, hpair⟩
    subst heq
    obtain ⟨p₁, hp₁, hpair₁⟩ := hy₁
    have hpeq : p = p₁ := by
      rcases hpair with ⟨aa₁, ab₁, haa₁, hab₁, hpp₁⟩
      rcases hpair₁ with ⟨aa₂, ab₂, haa₂, hab₂, hpp₂⟩
      have haa : aa₁ = aa₂ := pair_unique hM haa₁ haa₂
      have hab : ab₁ = ab₂ := pair_unique hM hab₁ hab₂
      subst haa; subst hab
      exact pair_unique hM hpp₁ hpp₂
    rwa [hpeq]

private theorem vstage_step_exists (hM : Model E) [Nonempty V] {α β : V}
    (hα : Ordinal E α) (hβ : E β α)
    (hPrev : ∀ γ, E γ β → ∃ v, VVal E γ v) :
    ∃ v, ∀ y, E y v ↔ ∃ γ, E γ β ∧ ∃ w, VVal E γ w ∧ SubSet E y w := by
  -- For each γ ∈ β, there is a unique w with VVal γ w, hence a unique P(w) = powerSet(w)!
  -- Formula: ∃ w, fVVal 0 w ∧ ∀ y, y ∈ 1 ↔ y ⊆ w
  let fPowV : Formula :=
    .ex (.and (fVVal 1 0) (.all (fIff (.mem 0 3) (fSub 0 1))))
  have hPowVBd : Bound fPowV 2 :=
    ⟨bound_fVVal (by omega) (by omega),
     ⟨⟨⟨by omega, by omega⟩, bound_fSub (by omega) (by omega)⟩,
      ⟨bound_fSub (by omega) (by omega), ⟨by omega, by omega⟩⟩⟩⟩
  have hFunc : ∀ x y₁ y₂,
      eval E fPowV (pushValue (pushValue (pushParams (fun _ => arbV) []) y₁) x) →
      eval E fPowV (pushValue (pushValue (pushParams (fun _ => arbV) []) y₂) x) →
      y₁ = y₂ := by
    intro x y₁ y₂ ⟨w₁, hw₁', hp₁⟩ ⟨w₂, hw₂', hp₂⟩
    have hw₁ : VVal E x w₁ := (eval_fVVal _ _ _).mp hw₁'
    have hw₂ : VVal E x w₂ := (eval_fVVal _ _ _).mp hw₂'
    rcases hw₁ with ⟨x₁', f₁, hs₁, hvs₁, hat₁⟩
    rcases hw₂ with ⟨x₂', f₂, hs₂, hvs₂, hat₂⟩
    have hw : w₁ = w₂ := vstage_agree hM hvs₁ hvs₂ x
      ((hs₁ x).mpr (Or.inr rfl)) ((hs₂ x).mpr (Or.inr rfl)) w₁ w₂ hat₁ hat₂
    subst hw
    apply ax_ext hM
    intro z
    exact ⟨fun hz => (hp₂ z).2 ((hp₁ z).1 hz), fun hz => (hp₁ z).2 ((hp₂ z).1 hz)⟩
  obtain ⟨B, hB⟩ := ax_rep hM 0 fPowV hPowVBd [] rfl hFunc β
  obtain ⟨U, hU⟩ := ax_union hM B
  refine ⟨U, fun y => ?_⟩
  rw [hU]
  constructor
  · rintro ⟨P, hPB, hyP⟩
    obtain ⟨γ, hγβ, w, hw', hP⟩ := (hB P).mp hPB
    exact ⟨γ, hγβ, w, (eval_fVVal _ _ _).mp hw', (hP y).1 hyP⟩
  · rintro ⟨γ, hγβ, w, hw, hsub⟩
    obtain ⟨P, hP⟩ := ax_power hM w
    refine ⟨P, (hB P).mpr ⟨γ, hγβ, w, (eval_fVVal _ _ _).mpr hw, fun z => ⟨(hP z).mp, (hP z).mpr⟩⟩,
      (hP y).mpr hsub⟩

private theorem vstage_exists (hM : Model E) [Nonempty V] :
    ∀ α : V, Ordinal E α → ∃ f, VStage E f α := by
  intro α hα
  obtain ⟨α', hα'⟩ := succ_exists hM α
  -- Bad(β) := ¬ ∃ f, VStage E f β
  let fNoStage : Formula := fNot (.ex (fVStage 0 1))
  have hNoStageBd : Bound fNoStage 1 := ⟨bound_fVStage (by omega) (by omega), trivial⟩
  obtain ⟨B, hB⟩ := ax_sep hM 0 fNoStage hNoStageBd [] rfl α'
  apply Classical.byContradiction
  intro hNoα
  have hBne : ∃ β, E β B := ⟨α, (hB α).mpr ⟨(hα' α).mpr (Or.inr rfl), fun ⟨f, hf⟩ =>
    hNoα ⟨f, (eval_fVStage _ _ _).mp hf⟩⟩⟩
  obtain ⟨β, hβB, hmin⟩ := ax_found hM hBne
  obtain ⟨hβα', hNoβ⟩ := (hB β).mp hβB
  have hβOrd : Ordinal E β := ordinal_elem (ordinal_succ hα hα') hβα'
  -- Every γ ∈ β has a VStage on succ γ, hence a VVal!
  have hPrevStage : ∀ γ, E γ β → ∃ f, VStage E f γ := by
    intro γ hγβ
    apply Classical.byContradiction
    intro hno
    have hγα' : E γ α' := (ordinal_succ hα hα').1 β hβα' γ hγβ
    exact hmin γ hγβ ((hB γ).mpr ⟨hγα', fun ⟨f, hf⟩ => hno ⟨f, (eval_fVStage _ _ _).mp hf⟩⟩)
  -- First show every γ ∈ β has a VVal!
  -- Wait: if γ ∈ β, we only know VStage on γ, NOT on succ γ (unless succ γ ∈ β)!
  -- We can define the value at γ directly from the VStage f on γ: v_γ = ⋃_{δ ∈ γ} P(f(δ))!
  -- Better: define VValAt γ v := ∃ f, VStage f γ ∧ ∀ y, y ∈ v ↔ ∃ δ ∈ γ, ∃ w, At f δ w ∧ y ⊆ w!
  let fVValAt : Formula :=
    .ex (.and (fVStage 0 1)
      (.all (fIff (.mem 0 3) (.ex (.and (.mem 0 2) (.ex (.and (fAt 2 1 0) (fSub 2 0))))))))
  have hVValAtBd : Bound fVValAt 2 :=
    ⟨bound_fVStage (by omega) (by omega),
     ⟨⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega), bound_fSub (by omega) (by omega)⟩⟩⟩,
      ⟨⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega), bound_fSub (by omega) (by omega)⟩⟩, ⟨by omega, by omega⟩⟩⟩⟩
  -- Graph pair formula: y is the ordered pair (x, v) where VValAt x v!
  let fPairV : Formula := .ex (.and (fOrderedPair 1 0 2) (rename (fun i => if i = 0 then 1 else if i = 1 then 0 else i + 1) fVValAt))
  -- Actually let's avoid rename! Just write fVValAt directly with (x=1, v=0, pair=2) inside fPairV!
  let fGraph : Formula :=
    .ex (.and (fOrderedPair 1 0 2)
      (.ex (.and (fVStage 0 2)
        (.all (fIff (.mem 0 2) (.ex (.and (.mem 0 4) (.ex (.and (fAt 3 1 0) (fSub 2 0))))))))))
  have hGraphBd : Bound fGraph 2 :=
    ⟨bound_fOrderedPair (by omega) (by omega) (by omega),
     bound_fVStage (by omega) (by omega),
     ⟨⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega), bound_fSub (by omega) (by omega)⟩⟩⟩,
      ⟨⟨⟨by omega, by omega⟩, ⟨bound_fAt (by omega) (by omega) (by omega), bound_fSub (by omega) (by omega)⟩⟩, ⟨by omega, by omega⟩⟩⟩⟩
  have hGraphFunc : ∀ x p₁ p₂,
      eval E fGraph (pushValue (pushValue (pushParams (fun _ => arbV) []) p₁) x) →
      eval E fGraph (pushValue (pushValue (pushParams (fun _ => arbV) []) p₂) x) →
      p₁ = p₂ := by
    intro x p₁ p₂ ⟨v₁, hp₁', f₁, hf₁', hv₁⟩ ⟨v₂, hp₂', f₂, hf₂', hv₂⟩
    have hf₁ : VStage E f₁ x := (eval_fVStage _ _ _).mp hf₁'
    have hf₂ : VStage E f₂ x := (eval_fVStage _ _ _).mp hf₂'
    have hfeq : f₁ = f₂ := vstage_unique hM hf₁ hf₂
    subst hfeq
    have hveq : v₁ = v₂ := by
      apply ax_ext hM
      intro y
      exact ⟨fun h => (hv₂ y).2 ((hv₁ y).1 h), fun h => (hv₁ y).2 ((hv₂ y).1 h)⟩
    subst hveq
    have hp₁ : OrderedPair E x v₁ p₁ := (eval_fOrderedPair _ _ _ _).mp hp₁'
    have hp₂ : OrderedPair E x v₁ p₂ := (eval_fOrderedPair _ _ _ _).mp hp₂'
    rcases hp₁ with ⟨aa₁, ab₁, haa₁, hab₁, hpp₁⟩
    rcases hp₂ with ⟨aa₂, ab₂, haa₂, hab₂, hpp₂⟩
    have haa : aa₁ = aa₂ := pair_unique hM haa₁ haa₂
    have hab : ab₁ = ab₂ := pair_unique hM hab₁ hab₂
    subst haa; subst hab
    exact pair_unique hM hpp₁ hpp₂
  obtain ⟨F, hF⟩ := ax_rep hM 0 fGraph hGraphBd [] rfl hGraphFunc β
  -- For every γ ∈ β, show ∃ v, VValAt γ v (using Replacement on γ with f_γ!)
  have hHasVal : ∀ γ, E γ β → ∃ v f_γ, VStage E f_γ γ ∧
      ∀ y, E y v ↔ ∃ δ, E δ γ ∧ ∃ w, At E f_γ δ w ∧ SubSet E y w := by
    intro γ hγβ
    obtain ⟨f_γ, hf_γ⟩ := hPrevStage γ hγβ
    -- Replacement on γ: δ ↦ P(f_γ(δ))
    let fPowAt : Formula := .ex (.and (fAt 3 1 0) (.all (fIff (.mem 0 3) (fSub 0 1))))
    have hPowAtBd : Bound fPowAt 3 :=
      ⟨bound_fAt (by omega) (by omega) (by omega),
       ⟨⟨⟨by omega, by omega⟩, bound_fSub (by omega) (by omega)⟩,
        ⟨bound_fSub (by omega) (by omega), ⟨by omega, by omega⟩⟩⟩⟩
    have hPowFunc : ∀ δ P₁ P₂,
        eval E fPowAt (pushValue (pushValue (pushParams (fun _ => arbV) [f_γ]) P₁) δ) →
        eval E fPowAt (pushValue (pushValue (pushParams (fun _ => arbV) [f_γ]) P₂) δ) →
        P₁ = P₂ := by
      intro δ P₁ P₂ ⟨w₁, hw₁', hP₁⟩ ⟨w₂, hw₂', hP₂⟩
      have hw₁ : At E f_γ δ w₁ := (eval_fAt _ _ _ _).mp hw₁'
      have hw₂ : At E f_γ δ w₂ := (eval_fAt _ _ _ _).mp hw₂'
      obtain ⟨_, _, hδγ, hpair₁⟩ := hf_γ.2.1.2 _ hw₁.choose_spec.1
      have hδeq : δ = _ := (orderedPair_inj hM hw₁.choose_spec.2 hpair₁).1
      -- Direct: use hf_γ.2.1.1!
      have hδmem : E δ γ := by
        obtain ⟨q, hqf, hqpair⟩ := hw₁
        obtain ⟨x', y', hx'γ, hx'pair⟩ := hf_γ.2.1.2 q hqf
        have hxeq := (orderedPair_inj hM hqpair hx'pair).1
        rwa [hxeq]
      obtain ⟨w0, _, huniq⟩ := hf_γ.2.1.1 δ hδmem
      have heq1 := huniq w₁ hw₁
      have heq2 := huniq w₂ hw₂
      subst heq1; subst heq2
      apply ax_ext hM; intro y
      exact ⟨fun h => (hP₂ y).2 ((hP₁ y).1 h), fun h => (hP₁ y).2 ((hP₂ y).1 h)⟩
    obtain ⟨B_γ, hB_γ⟩ := ax_rep hM 1 fPowAt hPowAtBd [f_γ] rfl hPowFunc γ
    obtain ⟨v, hv⟩ := ax_union hM B_γ
    refine ⟨v, f_γ, hf_γ, fun y => ?_⟩
    rw [hv]
    constructor
    · rintro ⟨P, hPB, hyP⟩
      obtain ⟨δ, hδγ, w, hw', hP⟩ := (hB_γ P).mp hPB
      exact ⟨δ, hδγ, w, (eval_fAt _ _ _ _).mp hw', (hP y).1 hyP⟩
    · rintro ⟨δ, hδγ, w, hw, hsub⟩
      obtain ⟨P, hP⟩ := ax_power hM w
      exact ⟨P, (hB_γ P).mpr ⟨δ, hδγ, w, (eval_fAt _ _ _ _).mpr hw, fun z => ⟨(hP z).mp, (hP z).mpr⟩⟩,
        (hP y).mpr hsub⟩
  -- Now prove VStage E F β!
  have hFStage : VStage E F β := by
    refine ⟨hβOrd, ⟨?_, ?_⟩, ?_⟩
    · intro γ hγβ
      obtain ⟨v, f_γ, hf_γ, hv⟩ := hHasVal γ hγβ
      obtain ⟨p, hp⟩ := orderedPair_exists hM γ v
      have hpF : E p F := (hF p).mpr ⟨γ, hγβ, v, (eval_fOrderedPair _ _ _ _).mpr hp, f_γ,
        (eval_fVStage _ _ _).mpr hf_γ, fun y =>
          ⟨fun h => let ⟨δ, hδ, w, hw, hsub⟩ := (hv y).mp h; ⟨δ, hδ, w, (eval_fAt _ _ _ _).mpr hw, hsub⟩,
           fun ⟨δ, hδ, w, hw, hsub⟩ => (hv y).mpr ⟨δ, hδ, w, (eval_fAt _ _ _ _).mp hw, hsub⟩⟩⟩
      refine ⟨v, ⟨p, hpF, hp⟩, fun z ⟨q, hqF, hq⟩ => ?_⟩
      obtain ⟨γ', _, v', hq', f', hf'', hv'⟩ := (hF q).mp hqF
      have hqop : OrderedPair E γ' v' q := (eval_fOrderedPair _ _ _ _).mp hq'
      obtain ⟨hγγ', hzv'⟩ := orderedPair_inj hM hq hqop
      subst hγγ'; subst hzv'
      have hfeq : f' = f_γ := vstage_unique hM ((eval_fVStage _ _ _).mp hf'') hf_γ
      subst hfeq
      apply ax_ext hM; intro y
      exact ⟨fun h => let ⟨δ, hδ, w, hw, hsub⟩ := (hv' y).1 h; (hv y).mpr ⟨δ, hδ, w, (eval_fAt _ _ _ _).mp hw, hsub⟩,
             fun h => let ⟨δ, hδ, w, hw, hsub⟩ := (hv y).mp h; (hv' y).2 ⟨δ, hδ, w, (eval_fAt _ _ _ _).mpr hw, hsub⟩⟩
    · intro p hpF
      obtain ⟨γ, hγβ, v, hp', _, _, _⟩ := (hF p).mp hpF
      exact ⟨γ, v, hγβ, (eval_fOrderedPair _ _ _ _).mp hp'⟩
    · intro γ hγβ v ⟨p, hpF, hp⟩ y
      obtain ⟨γ', _, v', hp', f_γ, hf_γ', hv⟩ := (hF p).mp hpF
      obtain ⟨hγγ', hvv'⟩ := orderedPair_inj hM hp ((eval_fOrderedPair _ _ _ _).mp hp')
      subst hγγ'; subst hvv'
      have hf_γ : VStage E f_γ γ := (eval_fVStage _ _ _).mp hf_γ'
      -- Show F agrees with f_γ on all δ ∈ γ!
      have hF_eq_fγ : ∀ δ, E δ γ → ∀ w, At E F δ w ↔ At E f_γ δ w := by
        intro δ hδγ w
        have hδβ : E δ β := hβOrd.1 γ hγβ δ hδγ
        constructor
        · rintro ⟨q, hqF, hq⟩
          obtain ⟨δ', _, w', hq', f_δ, hf_δ', hw'⟩ := (hF q).mp hqF
          obtain ⟨hδδ', hww'⟩ := orderedPair_inj hM hq ((eval_fOrderedPair _ _ _ _).mp hq')
          subst hδδ'; subst hww'
          have hf_δ : VStage E f_δ δ := (eval_fVStage _ _ _).mp hf_δ'
          obtain ⟨w0, hw0, _⟩ := hf_γ.2.1.1 δ hδγ
          have hweq : w = w0 := by
            apply ax_ext hM; intro z
            rw [hf_γ.2.2 δ hδγ w0 hw0 z]
            constructor
            · intro hz
              obtain ⟨η, hηδ, u, hu', hsub⟩ := (hw' z).1 hz
              have hu : At E f_δ η u := (eval_fAt _ _ _ _).mp hu'
              have hηγ : E η γ := (ordinal_elem hβOrd hγβ).1 δ hδγ η hηδ
              obtain ⟨u2, hu2, _⟩ := hf_γ.2.1.1 η hηγ
              have hueq := vstage_agree hM hf_δ hf_γ η hηδ hηγ u u2 hu hu2
              subst hueq
              exact ⟨η, hηδ, u, hu2, hsub⟩
            · rintro ⟨η, hηδ, u2, hu2, hsub⟩
              obtain ⟨u, hu, _⟩ := hf_δ.2.1.1 η hηδ
              have hηγ : E η γ := (ordinal_elem hβOrd hγβ).1 δ hδγ η hηδ
              have hueq := vstage_agree hM hf_δ hf_γ η hηδ hηγ u u2 hu hu2
              subst hueq
              exact (hw' z).2 ⟨η, hηδ, u, (eval_fAt _ _ _ _).mpr hu, hsub⟩
          rwa [hweq]
        · intro hw
          have hExF : ∃ wF, At E F δ wF := by
            obtain ⟨v0, f0, hf0, hv0⟩ := hHasVal δ hδβ
            obtain ⟨q, hq⟩ := orderedPair_exists hM δ v0
            have hqF : E q F := (hF q).mpr ⟨δ, hδβ, v0, (eval_fOrderedPair _ _ _ _).mpr hq, f0,
              (eval_fVStage _ _ _).mpr hf0, fun z =>
                ⟨fun h => let ⟨η, hη, u, hu, hsub⟩ := (hv0 z).mp h; ⟨η, hη, u, (eval_fAt _ _ _ _).mpr hu, hsub⟩,
                 fun ⟨η, hη, u, hu, hsub⟩ => (hv0 z).mpr ⟨η, hη, u, (eval_fAt _ _ _ _).mp hu, hsub⟩⟩⟩
            exact ⟨v0, ⟨q, hqF, hq⟩⟩
          obtain ⟨wF, hwF⟩ := hExF
          -- We already know At F δ wF → At f_γ δ wF, and f_γ is functional!
          have hwF' : At E f_γ δ wF := by
            obtain ⟨q, hqF, hq⟩ := hwF
            obtain ⟨δ', _, w', hq', f_δ, hf_δ', hw'⟩ := (hF q).mp hqF
            obtain ⟨hδδ', hww'⟩ := orderedPair_inj hM hq ((eval_fOrderedPair _ _ _ _).mp hq')
            subst hδδ'; subst hww'
            have hf_δ : VStage E f_δ δ := (eval_fVStage _ _ _).mp hf_δ'
            obtain ⟨w0, hw0, _⟩ := hf_γ.2.1.1 δ hδγ
            have hweq : wF = w0 := by
              apply ax_ext hM; intro z
              rw [hf_γ.2.2 δ hδγ w0 hw0 z]
              constructor
              · intro hz
                obtain ⟨η, hηδ, u, hu', hsub⟩ := (hw' z).1 hz
                have hu : At E f_δ η u := (eval_fAt _ _ _ _).mp hu'
                have hηγ : E η γ := (ordinal_elem hβOrd hγβ).1 δ hδγ η hηδ
                obtain ⟨u2, hu2, _⟩ := hf_γ.2.1.1 η hηγ
                have hueq := vstage_agree hM hf_δ hf_γ η hηδ hηγ u u2 hu hu2
                subst hueq; exact ⟨η, hηδ, u, hu2, hsub⟩
              · rintro ⟨η, hηδ, u2, hu2, hsub⟩
                obtain ⟨u, hu, _⟩ := hf_δ.2.1.1 η hηδ
                have hηγ : E η γ := (ordinal_elem hβOrd hγβ).1 δ hδγ η hηδ
                have hueq := vstage_agree hM hf_δ hf_γ η hηδ hηγ u u2 hu hu2
                subst hueq; exact (hw' z).2 ⟨η, hηδ, u, (eval_fAt _ _ _ _).mpr hu, hsub⟩
            rwa [hweq]
          obtain ⟨_, _, huniq⟩ := hf_γ.2.1.1 δ hδγ
          have h1 := huniq w hw
          have h2 := huniq wF hwF'
          rwa [h1, ← h2]
      constructor
      · intro hy
        obtain ⟨δ, hδγ, w, hw', hsub⟩ := (hv y).1 hy
        exact ⟨δ, hδγ, w, (hF_eq_fγ δ hδγ w).mpr ((eval_fAt _ _ _ _).mp hw'), hsub⟩
      · rintro ⟨δ, hδγ, w, hw, hsub⟩
        exact (hv y).2 ⟨δ, hδγ, w, (eval_fAt _ _ _ _).mpr ((hF_eq_fγ δ hδγ w).mp hw), hsub⟩
  exact hNoβ ⟨F, (eval_fVStage _ _ _).mpr hFStage⟩

private theorem vval_exists (hM : Model E) [Nonempty V] {α : V} (hα : Ordinal E α) :
    ∃ v, VVal E α v := by
  obtain ⟨α', hα'⟩ := succ_exists hM α
  obtain ⟨f, hf⟩ := vstage_exists hM α' (ordinal_succ hα hα')
  obtain ⟨v, hv, _⟩ := hf.2.1.1 α ((hα' α).mpr (Or.inr rfl))
  exact ⟨v, α', f, hα', hf, hv⟩

private theorem vval_unique (hM : Model E) [Nonempty V] {α v₁ v₂ : V}
    (h1 : VVal E α v₁) (h2 : VVal E α v₂) : v₁ = v₂ := by
  rcases h1 with ⟨α₁', f₁, hs₁, hvs₁, hat₁⟩
  rcases h2 with ⟨α₂', f₂, hs₂, hvs₂, hat₂⟩
  exact vstage_agree hM hvs₁ hvs₂ α ((hs₁ α).mpr (Or.inr rfl)) ((hs₂ α).mpr (Or.inr rfl)) v₁ v₂ hat₁ hat₂

private theorem vval_spec (hM : Model E) [Nonempty V] {α v : V} (hv : VVal E α v) :
    ∀ y, E y v ↔ ∃ γ, E γ α ∧ ∃ w, VVal E γ w ∧ SubSet E y w := by
  rcases hv with ⟨α', f, hs, hvs, hat⟩
  intro y
  rw [hvs.2.2 α ((hs α).mpr (Or.inr rfl)) v hat y]
  constructor
  · rintro ⟨γ, hγα, w, hw, hsub⟩
    have hγOrd : Ordinal E γ := ordinal_elem hvs.1 (hvs.1.1 α ((hs α).mpr (Or.inr rfl)) γ hγα)
    obtain ⟨w2, hw2⟩ := vval_exists hM hγOrd
    rcases hw2 with ⟨γ', f', hs', hvs', hat'⟩
    have hweq : w = w2 := vstage_agree hM hvs hvs' γ (hvs.1.1 α ((hs α).mpr (Or.inr rfl)) γ hγα)
      ((hs' γ).mpr (Or.inr rfl)) w w2 hw hat'
    subst hweq
    exact ⟨γ, hγα, w, ⟨γ', f', hs', hvs', hat'⟩, hsub⟩
  · rintro ⟨γ, hγα, w, ⟨γ', f', hs', hvs', hat'⟩, hsub⟩
    have hγα' : E γ α' := hvs.1.1 α ((hs α).mpr (Or.inr rfl)) γ hγα
    obtain ⟨w1, hw1, _⟩ := hvs.2.1.1 γ hγα'
    have hweq : w1 = w := vstage_agree hM hvs hvs' γ hγα' ((hs' γ).mpr (Or.inr rfl)) w1 w hw1 hat'
    subst hweq
    exact ⟨γ, hγα, w1, hw1, hsub⟩

private theorem vval_mono (hM : Model E) [Nonempty V] {α β v w : V}
    (hαβ : E α β) (hv : VVal E α v) (hw : VVal E β w) : SubSet E v w := by
  intro x hxv
  -- x ∈ v → ∃ γ ∈ α, ∃ u, VVal γ u ∧ x ⊆ u. Since β is an ordinal and α ∈ β, γ ∈ β!
  rcases hw with ⟨β', f, hs, hvs, hat⟩
  have hβOrd : Ordinal E β := ordinal_elem hvs.1 ((hs β).mpr (Or.inr rfl))
  obtain ⟨γ, hγα, u, hu, hsub⟩ := (vval_spec hM hv x).mp hxv
  exact (vval_spec hM ⟨β', f, hs, hvs, hat⟩ x).mpr ⟨γ, hβOrd.1 α hαβ γ hγα, u, hu, hsub⟩

/-! ### 7. Generic ω-Recursion and Transitive Closure + Exhaustion of `V` -/

private theorem omega_induction (hM : Model E) [Nonempty V] {w : V} (hw : Omega E w)
    (n : Nat) (body : Formula) (hbd : Bound body (n + 1)) (ps : List V) (hlen : ps.length = n)
    (hZero : ∀ z, Empty E z → eval E body (pushValue (pushParams (fun _ => arbV) ps) z))
    (hStep : ∀ x y, E x w → Succ E x y →
      eval E body (pushValue (pushParams (fun _ => arbV) ps) x) →
      eval E body (pushValue (pushParams (fun _ => arbV) ps) y)) :
    ∀ x, E x w → eval E body (pushValue (pushParams (fun _ => arbV) ps) x) := by
  obtain ⟨A, hA⟩ := ax_sep hM n body hbd ps hlen w
  have hInd : Inductive E A := by
    refine ⟨?_, ?_⟩
    · obtain ⟨z, hz, hzw⟩ := hw.1.1
      exact ⟨z, hz, (hA z).mpr ⟨hzw, hZero z hz⟩⟩
    · intro x hxA
      obtain ⟨hxw, hPx⟩ := (hA x).mp hxA
      obtain ⟨y, hxy, hyw⟩ := hw.1.2 x hxw
      exact ⟨y, hxy, (hA y).mpr ⟨hyw, hStep x y hxw hxy hPx⟩⟩
  intro x hxw
  exact ((hA x).mp (hw.2 A hInd x hxw)).2

-- Generic ω-recursion for a definable step relation `Step(prev, next)`!
private theorem omega_recursion (hM : Model E) [Nonempty V] {w : V} (hw : Omega E w)
    (n : Nat) (fStep : Formula) (hStepBd : Bound fStep (n + 2)) (ps : List V) (hlen : ps.length = n)
    (hStepTotal : ∀ x, ∃ y, eval E fStep (pushValue (pushValue (pushParams (fun _ => arbV) ps) y) x))
    (hStepFunc : ∀ x y₁ y₂,
      eval E fStep (pushValue (pushValue (pushParams (fun _ => arbV) ps) y₁) x) →
      eval E fStep (pushValue (pushValue (pushParams (fun _ => arbV) ps) y₂) x) →
      y₁ = y₂)
    (x0 : V) :
    ∃ F : V, FunctionOn E F w ∧
      (∀ z, Empty E z → At E F z x0) ∧
      (∀ k k', E k w → Succ E k k' → ∀ a b, At E F k a → At E F k' b →
        eval E fStep (pushValue (pushValue (pushParams (fun _ => arbV) ps) b) a)) := by
  -- Define FiniteRec(m, f) for m ∈ w:
  -- ∃ dom, Succ m dom ∧ FunctionOn f dom ∧ (∃ z, Empty z ∧ At f z x0) ∧
  --   ∀ k ∈ m, ∀ k', Succ k k' → ∀ a b, At f k a → At f k' b → Step(a, b)
  -- Wait: inside fFinRec, var 0 = m, var 1 = f, var 2 = x0, var (3+i) = ps[i]!
  -- Better: pass x0 as an extra parameter: ps' = x0 :: ps (length n + 1)!
  -- Inside fSeq(m, f) with params x0 :: ps: var 0 = m, var 1 = f, var 2 = x0, var (3+i) = ps[i]
  -- When renaming fStep (Bound n+2: 0=prev, 1=next, 2+i=ps[i]) under 6 binders (m, f, dom, k, k', a, b):
  -- Wait: inside fFinRec (Bound n+3: 0=m, 1=f, 2=x0, 3+i=ps[i]):
  --   ∃ dom (idx 0; m=1, f=2, x0=3, ps[i]=4+i):
  --     fSucc 1 0 ∧ fFunctionOn 2 0 ∧ (∃ z, fEmpty 0 ∧ fAt 3 0 4) ∧
  --     ∀ k (k=0, dom=1, m=2, f=3, x0=4, ps[i]=5+i): k ∈ m →
  --       ∀ k' (k'=0, k=1, dom=2, m=3, f=4, x0=5, ps[i]=6+i): fSucc 1 0 →
  --         ∀ a (a=0, k'=1, k=2, dom=3, m=4, f=5, x0=6, ps[i]=7+i): fAt 5 2 0 →
  --           ∀ b (b=0, a=1, k'=2, k=3, dom=4, m=5, f=6, x0=7, ps[i]=8+i): fAt 6 2 0 →
  --             rename (0=>1, 1=>0, j+2=>j+8) fStep
  let mapStep : Nat → Nat | 0 => 1 | 1 => 0 | j + 2 => j + 8
  let fFinRec : Formula :=
    .ex (.and (fSucc 1 0) (.and (fFunctionOn 2 0)
      (.and (.ex (.and (fEmpty 0) (fAt 3 0 4)))
        (.all (.imp (.mem 0 2)
          (.all (.imp (fSucc 1 0)
            (.all (.imp (fAt 5 2 0)
              (.all (.imp (fAt 6 2 0) (rename mapStep fStep))))))))))))
  have hFinRecBd : Bound fFinRec (n + 3) := by
    refine ⟨bound_fSucc (by omega) (by omega), bound_fFunctionOn (by omega) (by omega),
      ⟨bound_fEmpty (by omega), bound_fAt (by omega) (by omega) (by omega)⟩,
      ⟨⟨by omega, by omega⟩, ⟨bound_fSucc (by omega) (by omega),
       ⟨bound_fAt (by omega) (by omega) (by omega),
        ⟨bound_fAt (by omega) (by omega) (by omega), ?_⟩⟩⟩⟩⟩
    apply bound_rename fStep (n + 2) (n + 8) mapStep hStepBd
    intro i hi
    cases i with
    | zero => simp [mapStep]
    | succ k => cases k with | zero => simp [mapStep] | succ j => simp [mapStep]; omega
  -- Helper semantics of fFinRec
  let sBase := pushParams (fun _ => arbV) ps
  let IsFinRec (m f : V) : Prop :=
    ∃ dom, Succ E m dom ∧ FunctionOn E f dom ∧
      (∃ z, Empty E z ∧ At E f z x0) ∧
      ∀ k, E k m → ∀ k', Succ E k k' → ∀ a b, At E f k a → At E f k' b →
        eval E fStep (pushValue (pushValue sBase b) a)
  have eval_fFinRec : ∀ m f,
      eval E fFinRec (pushValue (pushValue (pushValue sBase x0) f) m) ↔ IsFinRec m f := by
    intro m f
    constructor
    · rintro ⟨dom, hdom, hfun, ⟨z, hz, hat0⟩, hst⟩
      refine ⟨dom, (eval_fSucc _ _ _).mp hdom, (eval_fFunctionOn _ _ _).mp hfun,
        ⟨z, hz, (eval_fAt _ _ _ _).mp hat0⟩, fun k hk k' hkk' a b ha hb => ?_⟩
      have hs := hst k hk k' ((eval_fSucc _ _ _).mpr hkk') a ((eval_fAt _ _ _ _).mpr ha) b ((eval_fAt _ _ _ _).mpr hb)
      rw [eval_rename] at hs
      have hfn : (fun i => pushValue (pushValue (pushValue (pushValue (pushValue (pushValue (pushValue (pushValue sBase x0) f) m) dom) k) k') a) b (mapStep i)) =
          pushValue (pushValue sBase b) a := by
        funext i; cases i with
        | zero => rfl
        | succ j => cases j with | zero => rfl | succ r => rfl
      rwa [hfn] at hs
    · rintro ⟨dom, hdom, hfun, ⟨z, hz, hat0⟩, hst⟩
      refine ⟨dom, (eval_fSucc _ _ _).mpr hdom, (eval_fFunctionOn _ _ _).mpr hfun,
        ⟨z, hz, (eval_fAt _ _ _ _).mpr hat0⟩, fun k hk k' hkk' a ha b hb => ?_⟩
      rw [eval_rename]
      have hfn : (fun i => pushValue (pushValue (pushValue (pushValue (pushValue (pushValue (pushValue (pushValue sBase x0) f) m) dom) k) k') a) b (mapStep i)) =
          pushValue (pushValue sBase b) a := by
        funext i; cases i with
        | zero => rfl
        | succ j => cases j with | zero => rfl | succ r => rfl
      rw [hfn]
      exact hst k hk k' ((eval_fSucc _ _ _).mp hkk') a b ((eval_fAt _ _ _ _).mp ha) ((eval_fAt _ _ _ _).mp hb)
  -- Prove ω is an ordinal (every element of ω is transitive and ω is transitive)!
  have hwTrans : TransSet E w := by
    -- A := { x ∈ w | x ⊆ w } is inductive!
    obtain ⟨A, hA⟩ := ax_sep hM 1 (fSub 0 1) (bound_fSub (by omega) (by omega)) [w] rfl w
    have hInd : Inductive E A := by
      refine ⟨?_, ?_⟩
      · obtain ⟨z, hz, hzw⟩ := hw.1.1
        exact ⟨z, hz, (hA z).mpr ⟨hzw, fun y hy => False.elim (hz y hy)⟩⟩
      · intro x hxA
        obtain ⟨hxw, hxsub⟩ := (hA x).mp hxA
        obtain ⟨y, hxy, hyw⟩ := hw.1.2 x hxw
        refine ⟨y, hxy, (hA y).mpr ⟨hyw, fun u hu => ?_⟩⟩
        cases (hxy u).mp hu with
        | inl hux => exact hxsub u hux
        | inr hux => subst hux; exact hxw
    intro x hxw u hux
    exact ((hA x).mp (hw.2 A hInd x hxw)).2 u hux
  have hwElemTrans : ∀ x, E x w → TransSet E x := by
    obtain ⟨A, hA⟩ := ax_sep hM 0 (fTrans 0) (bound_fTrans (by omega)) [] rfl w
    have hInd : Inductive E A := by
      refine ⟨?_, ?_⟩
      · obtain ⟨z, hz, hzw⟩ := hw.1.1
        exact ⟨z, hz, (hA z).mpr ⟨hzw, fun u hu => False.elim (hz u hu)⟩⟩
      · intro x hxA
        obtain ⟨hxw, htx⟩ := (hA x).mp hxA
        obtain ⟨y, hxy, hyw⟩ := hw.1.2 x hxw
        refine ⟨y, hxy, (hA y).mpr ⟨hyw, fun u hu v hv => ?_⟩⟩
        apply (hxy v).mpr
        cases (hxy u).mp hu with
        | inl hux => exact Or.inl (htx u hux v hv)
        | inr hux => subst hux; exact Or.inl hv
    intro x hxw
    exact ((hA x).mp (hw.2 A hInd x hxw)).2
  have hwOrd : Ordinal E w := ⟨hwTrans, hwElemTrans⟩
  -- 1. Existence of FinRec for every m ∈ w by omega_induction!
  -- Formula: ∃ f, fFinRec(m, f) [with params x0 :: ps, so var 0 = m, var 1 = x0, var 2+i = ps[i]]
  let mapEx : Nat → Nat | 0 => 1 | 1 => 0 | j + 2 => j + 2
  let fExRec : Formula := .ex (rename mapEx fFinRec)
  have hExRecBd : Bound fExRec (n + 2) := by
    apply bound_rename fFinRec (n + 3) (n + 3) mapEx hFinRecBd
    intro i hi; cases i with | zero => simp [mapEx] | succ k => cases k with | zero => simp [mapEx] | succ j => simp [mapEx]; omega
  have hExRec : ∀ m, E m w → ∃ f, IsFinRec m f := by
    have hInd := omega_induction hM hw (n + 1) fExRec hExRecBd (ps ++ [x0]) (by simp [hlen])
      (fun z hz => by
        obtain ⟨dom, hdom⟩ := succ_exists hM z
        obtain ⟨p0, hp0⟩ := orderedPair_exists hM z x0
        obtain ⟨f0, hf0⟩ := ax_pair hM p0 p0
        have hrec : IsFinRec z f0 := by
          refine ⟨dom, hdom, ⟨?_, ?_⟩, ⟨z, hz, p0, (hf0 p0).mpr (Or.inl rfl), hp0⟩, fun k hk => False.elim (hz k hk)⟩
          · intro x hx
            have hxz : x = z := by
              cases (hdom x).mp hx with | inl h => exact False.elim (hz x h) | inr h => exact h
            subst hxz
            refine ⟨x0, ⟨p0, (hf0 p0).mpr (Or.inl rfl), hp0⟩, fun y ⟨q, hqf, hq⟩ => ?_⟩
            have hqp : q = p0 := by cases (hf0 q).mp hqf with | inl h => exact h | inr h => exact h
            subst hqp
            exact (orderedPair_inj hM hq hp0).2
          · intro q hqf
            have hqp : q = p0 := by cases (hf0 q).mp hqf with | inl h => exact h | inr h => exact h
            subst hqp
            exact ⟨z, x0, (hdom z).mpr (Or.inr rfl), hp0⟩
        refine ⟨f0, ?_⟩
        rw [eval_rename, pushParams_append]
        have hfn : (fun i => pushValue (pushValue (pushParams sBase [x0]) z) f0 (mapEx i)) =
            pushValue (pushValue (pushValue sBase x0) f0) z := by
          funext i; cases i with | zero => rfl | succ k => cases k with | zero => rfl | succ j => rfl
        rw [hfn, eval_fFinRec]
        exact hrec)
      (fun m m' hmw hmm' hm => by
        obtain ⟨f, hf'⟩ := hm
        rw [eval_rename, pushParams_append] at hf'
        have hfn : (fun i => pushValue (pushValue (pushParams sBase [x0]) m) f (mapEx i)) =
            pushValue (pushValue (pushValue sBase x0) f) m := by
          funext i; cases i with | zero => rfl | succ k => cases k with | zero => rfl | succ j => rfl
        rw [hfn, eval_fFinRec] at hf'
        rcases hf' with ⟨dom, hdom, hfun, h0, hst⟩
        obtain ⟨a, ha, _⟩ := hfun.1 m ((hdom m).mpr (Or.inr rfl))
        obtain ⟨b, hb⟩ := hStepTotal a
        obtain ⟨pnew, hpnew⟩ := orderedPair_exists hM m' b
        obtain ⟨sp, hsp⟩ := ax_pair hM pnew pnew
        obtain ⟨f', hf'⟩ := binUnion_exists hM f sp
        obtain ⟨dom', hdom'⟩ := succ_exists hM m'
        have hrec' : IsFinRec m' f' := by
          have hm'_not_dom : ¬ E m' dom := by
            intro h
            cases (hdom m').mp h with
            | inl hlt => exact mem_asymm hM hlt ((hmm' m).mpr (Or.inr rfl))
            | inr heq => subst heq; exact mem_irrefl hM m' ((hmm' m').mpr (Or.inr rfl))
          have hAt_f' : ∀ x y, At E f' x y ↔ At E f x y ∨ (x = m' ∧ y = b) := by
            intro x y
            constructor
            · rintro ⟨q, hqf', hq⟩
              cases (hf' q).mp hqf' with
              | inl hqf => exact Or.inl ⟨q, hqf, hq⟩
              | inr hqsp =>
                have hqp : q = pnew := by cases (hsp q).mp hqsp with | inl h => exact h | inr h => exact h
                subst hqp
                exact Or.inr (orderedPair_inj hM hq hpnew)
            · intro h
              rcases h with ⟨q, hqf, hq⟩ | ⟨hx, hy⟩
              · exact ⟨q, (hf' q).mpr (Or.inl hqf), hq⟩
              · subst hx; subst hy; exact ⟨pnew, (hf' pnew).mpr (Or.inr ((hsp pnew).mpr (Or.inl rfl))), hpnew⟩
          refine ⟨dom', hdom', ⟨?_, ?_⟩, ?_, ?_⟩
          · intro x hx
            cases (hdom' x).mp hx with
            | inl hxm' =>
              have hxd : E x dom := by
                cases (hmm' x).mp hxm' with
                | inl hxm => exact (hdom x).mpr (Or.inl hxm)
                | inr hxe => exact (hdom x).mpr (Or.inr hxe)
              obtain ⟨y, hy, hu⟩ := hfun.1 x hxd
              refine ⟨y, (hAt_f' x y).mpr (Or.inl hy), fun z hz => ?_⟩
              rcases (hAt_f' x z).mp hz with hzf | ⟨hxm'eq, _⟩
              · exact hu z hzf
              · subst hxm'eq; exact False.elim (hm'_not_dom hxd)
            | inr hxe =>
              subst x
              refine ⟨b, (hAt_f' m' b).mpr (Or.inr ⟨rfl, rfl⟩), fun z hz => ?_⟩
              rcases (hAt_f' m' z).mp hz with ⟨q, hqf, hq⟩ | ⟨_, hzb⟩
              · obtain ⟨x', _, hx'd, hq'⟩ := hfun.2 q hqf
                have hxeq := (orderedPair_inj hM hq hq').1
                subst hxeq; exact False.elim (hm'_not_dom hx'd)
              · exact hzb
          · intro q hqf'
            cases (hf' q).mp hqf' with
            | inl hqf =>
              obtain ⟨x, y, hxd, hq⟩ := hfun.2 q hqf
              have hxm' : E x m' := by
                cases (hdom x).mp hxd with
                | inl h => exact (hmm' x).mpr (Or.inl h)
                | inr h => exact (hmm' x).mpr (Or.inr h)
              exact ⟨x, y, (hdom' x).mpr (Or.inl hxm'), hq⟩
            | inr hqsp =>
              have hqp : q = pnew := by cases (hsp q).mp hqsp with | inl h => exact h | inr h => exact h
              subst hqp
              exact ⟨m', b, (hdom' m').mpr (Or.inr rfl), hpnew⟩
          · obtain ⟨z, hz, hatz⟩ := h0
            exact ⟨z, hz, (hAt_f' z x0).mpr (Or.inl hatz)⟩
          · intro k hkm' k' hkk' u v hu hv
            cases (hmm' k).mp hkm' with
            | inl hkm =>
              have hk'd : E k' dom := by
                -- k ∈ m and Succ k k' → k' ∈ dom (since m' is an ordinal and k ∈ m ∈ m', wait: k' ∈ m ∨ k' = m!)
                have hmOrd : Ordinal E m := ordinal_elem hwOrd hmw
                have hkOrd : Ordinal E k := ordinal_elem hmOrd hkm
                have hk'Ord : Ordinal E k' := ordinal_succ hkOrd hkk'
                rcases ordinal_trichotomy hM hk'Ord hmOrd with h1 | h2 | h3
                · exact (hdom k').mpr (Or.inl h1)
                · exact (hdom k').mpr (Or.inr h2)
                · cases (hkk' m).mp h3 with
                  | inl hmk => exact False.elim (mem_asymm hM hkm hmk)
                  | inr hmk => rw [hmk] at hkm; exact False.elim (mem_irrefl hM k hkm)
              have hkd : E k dom := (hdom k).mpr (Or.inl hkm)
              have huf : At E f k u := by
                rcases (hAt_f' k u).mp hu with h | ⟨heq, _⟩
                · exact h
                · subst heq; exact False.elim (hm'_not_dom hkd)
              have hvf : At E f k' v := by
                rcases (hAt_f' k' v).mp hv with h | ⟨heq, _⟩
                · exact h
                · subst heq; exact False.elim (hm'_not_dom hk'd)
              exact hst k hkm k' hkk' u v huf hvf
            | inr hkm =>
              subst hkm
              have hk'eq : k' = m' := ax_ext hM (fun x => (hkk' x).trans (hmm' x).symm)
              subst k'
              have hua : u = a := by
                rcases (hAt_f' k u).mp hu with huf | ⟨heq, _⟩
                · obtain ⟨_, _, huq⟩ := hfun.1 k ((hdom k).mpr (Or.inr rfl))
                  exact (huq u huf).trans (huq a ha).symm
                · subst heq; exact False.elim (hm'_not_dom ((hdom k).mpr (Or.inr rfl)))
              have hvb : v = b := by
                rcases (hAt_f' m' v).mp hv with ⟨q, hqf, hq⟩ | ⟨_, h⟩
                · obtain ⟨x', _, hx'd, hq'⟩ := hfun.2 q hqf
                  have hxeq := (orderedPair_inj hM hq hq').1
                  subst hxeq; exact False.elim (hm'_not_dom hx'd)
                · exact h
              subst hua; subst hvb; exact hb
        refine ⟨f', ?_⟩
        rw [eval_rename, pushParams_append]
        have hfn : (fun i => pushValue (pushValue (pushParams sBase [x0]) m') f' (mapEx i)) =
            pushValue (pushValue (pushValue sBase x0) f') m' := by
          funext i; cases i with | zero => rfl | succ k => cases k with | zero => rfl | succ j => rfl
        rw [hfn, eval_fFinRec]
        exact hrec')
    intro m hmw
    obtain ⟨f, hf⟩ := hInd m hmw
    rw [eval_rename, pushParams_append] at hf
    have hfn : (fun i => pushValue (pushValue (pushParams sBase [x0]) m) f (mapEx i)) =
        pushValue (pushValue (pushValue sBase x0) f) m := by
      funext i; cases i with | zero => rfl | succ k => cases k with | zero => rfl | succ j => rfl
    rw [hfn, eval_fFinRec] at hf
    exact ⟨f, hf⟩
  -- 2. Agreement of any two FinRecs on common indices!
  have hAgree : ∀ m₁ f₁ m₂ f₂, E m₁ w → E m₂ w → IsFinRec m₁ f₁ → IsFinRec m₂ f₂ →
      ∀ k, E k w → ∀ a b, At E f₁ k a → At E f₂ k b → a = b := by
    intro m₁ f₁ m₂ f₂ hm₁ hm₂ h1 h2
    -- Use omega_induction on k ∈ w: ∀ a b, At f₁ k a → At f₂ k b → a = b!
    let fEqAt : Formula := .all (.all (.imp (fAt 3 2 1) (.imp (fAt 4 2 0) (.eq 1 0))))
    have hEqAtBd : Bound fEqAt 3 :=
      ⟨bound_fAt (by omega) (by omega) (by omega), ⟨bound_fAt (by omega) (by omega) (by omega), ⟨by omega, by omega⟩⟩⟩
    have hInd := omega_induction hM hw 2 fEqAt hEqAtBd [f₂, f₁] rfl
      (fun z hz a b ha hb => by
        obtain ⟨dom₁, hdom₁, hfun₁, ⟨z₁, hz₁, hat₁⟩, _⟩ := h1
        obtain ⟨dom₂, hdom₂, hfun₂, ⟨z₂, hz₂, hat₂⟩, _⟩ := h2
        have hz1eq : z = z₁ := ax_ext hM (fun u => ⟨fun h => False.elim (hz u h), fun h => False.elim (hz₁ u h)⟩)
        have hz2eq : z = z₂ := ax_ext hM (fun u => ⟨fun h => False.elim (hz u h), fun h => False.elim (hz₂ u h)⟩)
        subst hz1eq
        have ha' : At E f₁ z a := (eval_fAt _ _ _ _).mp ha
        have hb' : At E f₂ z b := (eval_fAt _ _ _ _).mp hb
        have hzd₁ : E z dom₁ := by
          obtain ⟨q, hq, hp⟩ := ha'; obtain ⟨x, _, hxd, hqp⟩ := hfun₁.2 q hq
          rwa [(orderedPair_inj hM hp hqp).1]
        have hzd₂ : E z dom₂ := by
          obtain ⟨q, hq, hp⟩ := hb'; obtain ⟨x, _, hxd, hqp⟩ := hfun₂.2 q hq
          rwa [(orderedPair_inj hM hp hqp).1]
        obtain ⟨_, _, hu₁⟩ := hfun₁.1 z hzd₁
        obtain ⟨_, _, hu₂⟩ := hfun₂.1 z hzd₂
        rw [← hz2eq] at hat₂
        exact (hu₁ a ha').trans ((hu₁ x0 hat₁).symm.trans ((hu₂ x0 hat₂).trans (hu₂ b hb').symm)))
      (fun k k' hkw hkk' ih a b ha hb => by
        have ha' : At E f₁ k' a := (eval_fAt _ _ _ _).mp ha
        have hb' : At E f₂ k' b := (eval_fAt _ _ _ _).mp hb
        rcases h1 with ⟨dom₁, hdom₁, hfun₁, _, hst₁⟩
        rcases h2 with ⟨dom₂, hdom₂, hfun₂, _, hst₂⟩
        have hk'd₁ : E k' dom₁ := by
          obtain ⟨q, hq, hp⟩ := ha'; obtain ⟨x, _, hxd, hqp⟩ := hfun₁.2 q hq
          rwa [(orderedPair_inj hM hp hqp).1]
        have hk'd₂ : E k' dom₂ := by
          obtain ⟨q, hq, hp⟩ := hb'; obtain ⟨x, _, hxd, hqp⟩ := hfun₂.2 q hq
          rwa [(orderedPair_inj hM hp hqp).1]
        have hkm₁ : E k m₁ := by
          cases (hdom₁ k').mp hk'd₁ with
          | inl h => exact (ordinal_elem hwOrd hm₁).1 k' h k ((hkk' k).mpr (Or.inr rfl))
          | inr h => subst h; exact (hkk' k).mpr (Or.inr rfl)
        have hkm₂ : E k m₂ := by
          cases (hdom₂ k').mp hk'd₂ with
          | inl h => exact (ordinal_elem hwOrd hm₂).1 k' h k ((hkk' k).mpr (Or.inr rfl))
          | inr h => subst h; exact (hkk' k).mpr (Or.inr rfl)
        obtain ⟨u₁, hu₁, _⟩ := hfun₁.1 k ((hdom₁ k).mpr (Or.inl hkm₁))
        obtain ⟨u₂, hu₂, _⟩ := hfun₂.1 k ((hdom₂ k).mpr (Or.inl hkm₂))
        have hu : u₁ = u₂ := ih u₁ u₂ ((eval_fAt _ _ _ _).mpr hu₁) ((eval_fAt _ _ _ _).mpr hu₂)
        subst hu
        exact hStepFunc u₁ a b (hst₁ k hkm₁ k' hkk' u₁ a hu₁ ha') (hst₂ k hkm₂ k' hkk' u₁ b hu₂ hb'))
    intro k hkw a b ha hb
    exact hInd k hkw a b ((eval_fAt _ _ _ _).mpr ha) ((eval_fAt _ _ _ _).mpr hb)
  -- 3. Collect the graph F on w by Replacement: m ↦ (m, f_m(m))!
  -- Pass ps ++ [x0, w] (length n + 2)! Under ∃ f (1) ∃ v (0): m=2, p=3, w=4, x0=5, ps[i]=6+i!
  let mapRecW : Nat → Nat | 0 => 2 | 1 => 1 | 2 => 5 | j + 3 => j + 6
  let fCollectW : Formula :=
    .and (.mem 0 2) (.ex (.ex (.and (fOrderedPair 2 0 3) (.and (fAt 1 2 0) (rename mapRecW fFinRec)))))
  have hCollectWBd : Bound fCollectW (n + 4) := by
    refine ⟨⟨by omega, by omega⟩, bound_fOrderedPair (by omega) (by omega) (by omega),
      bound_fAt (by omega) (by omega) (by omega), ?_⟩
    apply bound_rename fFinRec (n + 3) (n + 6) mapRecW hFinRecBd
    intro i hi
    cases i with
    | zero => simp [mapRecW]
    | succ k => cases k with
      | zero => simp [mapRecW]
      | succ j => cases j with | zero => simp [mapRecW] | succ r => simp [mapRecW]; omega
  have hColFunc : ∀ m p₁ p₂,
      eval E fCollectW (pushValue (pushValue (pushParams (fun _ => arbV) (ps ++ [x0, w])) p₁) m) →
      eval E fCollectW (pushValue (pushValue (pushParams (fun _ => arbV) (ps ++ [x0, w])) p₂) m) →
      p₁ = p₂ := by
    intro m p₁ p₂ ⟨hmw, f₁, v₁, hp₁', hat₁', hrec₁'⟩ ⟨_, f₂, v₂, hp₂', hat₂', hrec₂'⟩
    rw [pushParams_append] at hmw hrec₁' hrec₂'
    rw [eval_rename] at hrec₁' hrec₂'
    have hfn1 : (fun i => pushValue (pushValue (pushValue (pushValue (pushParams sBase [x0, w]) p₁) m) f₁) v₁ (mapRecW i)) =
        pushValue (pushValue (pushValue sBase x0) f₁) m := by
      funext i; cases i with
      | zero => rfl
      | succ k => cases k with | zero => rfl | succ j => cases j with | zero => rfl | succ r => rfl
    have hfn2 : (fun i => pushValue (pushValue (pushValue (pushValue (pushParams sBase [x0, w]) p₂) m) f₂) v₂ (mapRecW i)) =
        pushValue (pushValue (pushValue sBase x0) f₂) m := by
      funext i; cases i with
      | zero => rfl
      | succ k => cases k with | zero => rfl | succ j => cases j with | zero => rfl | succ r => rfl
    rw [hfn1, eval_fFinRec] at hrec₁'
    rw [hfn2, eval_fFinRec] at hrec₂'
    have hv : v₁ = v₂ := hAgree m f₁ m f₂ hmw hmw hrec₁' hrec₂' m hmw v₁ v₂
      ((eval_fAt _ _ _ _).mp hat₁') ((eval_fAt _ _ _ _).mp hat₂')
    subst hv
    rcases (eval_fOrderedPair _ _ _ _).mp hp₁' with ⟨aa₁, ab₁, haa₁, hab₁, hpp₁⟩
    rcases (eval_fOrderedPair _ _ _ _).mp hp₂' with ⟨aa₂, ab₂, haa₂, hab₂, hpp₂⟩
    have haa := pair_unique hM haa₁ haa₂
    have hab := pair_unique hM hab₁ hab₂
    subst haa; subst hab
    exact pair_unique hM hpp₁ hpp₂
  obtain ⟨F, hF⟩ := ax_rep hM (n + 2) fCollectW hCollectWBd (ps ++ [x0, w]) (by simp [hlen]) hColFunc w
  have hAtF : ∀ k v, At E F k v ↔ E k w ∧ ∃ f, IsFinRec k f ∧ At E f k v := by
    intro k v
    constructor
    · rintro ⟨p, hpF, hp⟩
      obtain ⟨k', hk'w, _, f, v', hp', hat', hrec'⟩ := (hF p).mp hpF
      obtain ⟨hkk', hvv'⟩ := orderedPair_inj hM hp ((eval_fOrderedPair _ _ _ _).mp hp')
      subst hkk'; subst hvv'
      rw [pushParams_append] at hrec'
      rw [eval_rename] at hrec'
      have hfn : (fun i => pushValue (pushValue (pushValue (pushValue (pushParams sBase [x0, w]) p) k) f) v (mapRecW i)) =
          pushValue (pushValue (pushValue sBase x0) f) k := by
        funext i; cases i with
        | zero => rfl
        | succ a => cases a with | zero => rfl | succ j => cases j with | zero => rfl | succ r => rfl
      rw [hfn, eval_fFinRec] at hrec'
      exact ⟨hk'w, f, hrec', (eval_fAt _ _ _ _).mp hat'⟩
    · rintro ⟨hkw, f, hrec, hat⟩
      obtain ⟨p, hp⟩ := orderedPair_exists hM k v
      refine ⟨p, (hF p).mpr ⟨k, hkw, ?_, f, v, (eval_fOrderedPair _ _ _ _).mpr hp,
        (eval_fAt _ _ _ _).mpr hat, ?_⟩, hp⟩
      · rw [pushParams_append]; exact hkw
      · rw [pushParams_append, eval_rename]
        have hfn : (fun i => pushValue (pushValue (pushValue (pushValue (pushParams sBase [x0, w]) p) k) f) v (mapRecW i)) =
            pushValue (pushValue (pushValue sBase x0) f) k := by
          funext i; cases i with
          | zero => rfl
          | succ a => cases a with | zero => rfl | succ j => cases j with | zero => rfl | succ r => rfl
        rw [hfn, eval_fFinRec]
        exact hrec
  refine ⟨F, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro k hkw
    obtain ⟨f, hrec⟩ := hExRec k hkw
    rcases hrec with ⟨dom, hdom, hfun, h0, hst⟩
    obtain ⟨v, hv, _⟩ := hfun.1 k ((hdom k).mpr (Or.inr rfl))
    refine ⟨v, (hAtF k v).mpr ⟨hkw, f, ⟨dom, hdom, hfun, h0, hst⟩, hv⟩, fun z hz => ?_⟩
    obtain ⟨_, f', hrec', hat'⟩ := (hAtF k z).mp hz
    exact hAgree k f' k f hkw hkw hrec' ⟨dom, hdom, hfun, h0, hst⟩ k hkw z v hat' hv
  · intro p hpF
    obtain ⟨k, hkw, _, _, v, hp', _, _⟩ := (hF p).mp hpF
    exact ⟨k, v, hkw, (eval_fOrderedPair _ _ _ _).mp hp'⟩
  · intro z hz
    obtain ⟨z', hz', hz'w⟩ := hw.1.1
    have hzeq : z = z' := ax_ext hM (fun u => ⟨fun h => False.elim (hz u h), fun h => False.elim (hz' u h)⟩)
    subst hzeq
    obtain ⟨f, hrec⟩ := hExRec z hz'w
    obtain ⟨dom, hdom, hfun, ⟨z0, hz0, hat0⟩, hst⟩ := hrec
    have hz0eq : z = z0 := ax_ext hM (fun u => ⟨fun h => False.elim (hz u h), fun h => False.elim (hz0 u h)⟩)
    subst hz0eq
    exact (hAtF z x0).mpr ⟨hz'w, f, ⟨dom, hdom, hfun, ⟨z, hz0, hat0⟩, hst⟩, hat0⟩
  · intro k k' hkw hkk' a b ha hb
    obtain ⟨_, f₁, hrec₁, hat₁⟩ := (hAtF k a).mp ha
    obtain ⟨hk'w, f₂, hrec₂, hat₂⟩ := (hAtF k' b).mp hb
    rcases hrec₂ with ⟨dom₂, hdom₂, hfun₂, h0₂, hst₂⟩
    obtain ⟨u, hu, _⟩ := hfun₂.1 k ((hdom₂ k).mpr (Or.inl ((hkk' k).mpr (Or.inr rfl))))
    have hua : a = u := hAgree k f₁ k' f₂ hkw hk'w hrec₁ ⟨dom₂, hdom₂, hfun₂, h0₂, hst₂⟩ k hkw a u hat₁ hu
    subst hua
    exact hst₂ k ((hkk' k).mpr (Or.inr rfl)) k' hkk' a b hu hat₂

private theorem tc_exists (hM : Model E) [Nonempty V] (x : V) :
    ∃ T : V, E x T ∧ TransSet E T := by
  obtain ⟨w, hw⟩ := ax_omega hM
  obtain ⟨sx, hsx⟩ := ax_pair hM x x
  -- Step: y = ⋃ x (var 0 = x, var 1 = y)
  let fUnionStep : Formula := .all (fIff (.mem 0 2) (.ex (.and (.mem 0 2) (.mem 1 0))))
  have hUStepBd : Bound fUnionStep 2 :=
    ⟨⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩⟩,
     ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ⟨by omega, by omega⟩⟩⟩
  obtain ⟨F, hFun, hF0, hFstep⟩ := omega_recursion hM hw 0 fUnionStep hUStepBd [] rfl
    (fun a => let ⟨u, hu⟩ := ax_union hM a; ⟨u, fun t => ⟨(hu t).mp, (hu t).mpr⟩⟩)
    (fun a u₁ u₂ h1 h2 => ax_ext hM (fun t => ⟨fun h => (h2 t).2 ((h1 t).1 h), fun h => (h1 t).2 ((h2 t).1 h)⟩))
    sx
  -- Collect range of F on w: B = { y | ∃ k ∈ w, At F k y }, then T = ⋃ B!
  obtain ⟨B, hB⟩ := ax_rep hM 1 (fAt 2 0 1) (bound_fAt (by omega) (by omega) (by omega)) [F] rfl
    (fun k y₁ y₂ h1 h2 => by
      have h1' : At E F k y₁ := (eval_fAt _ _ _ _).mp h1
      have h2' : At E F k y₂ := (eval_fAt _ _ _ _).mp h2
      have hkw : E k w := by
        obtain ⟨q, hqf, hqp⟩ := h1'; obtain ⟨x', _, hx'w, hqp'⟩ := hFun.2 q hqf
        rwa [(orderedPair_inj hM hqp hqp').1]
      obtain ⟨_, _, hu⟩ := hFun.1 k hkw
      exact (hu y₁ h1').trans (hu y₂ h2').symm) w
  obtain ⟨T, hT⟩ := ax_union hM B
  refine ⟨T, ?_, ?_⟩
  · obtain ⟨z, hz, hzw⟩ := hw.1.1
    exact (hT x).mpr ⟨sx, (hB sx).mpr ⟨z, hzw, (eval_fAt _ _ _ _).mpr (hF0 z hz)⟩, (hsx x).mpr (Or.inl rfl)⟩
  · intro u huT v hvu
    obtain ⟨A, hAB, huA⟩ := (hT u).mp huT
    obtain ⟨k, hkw, hFkA'⟩ := (hB A).mp hAB
    have hFkA : At E F k A := (eval_fAt _ _ _ _).mp hFkA'
    obtain ⟨k', hkk', hk'w⟩ := hw.1.2 k hkw
    obtain ⟨A', hFk'A', _⟩ := hFun.1 k' hk'w
    have hA' := hFstep k k' hkw hkk' A A' hFkA hFk'A'
    have hvA' : E v A' := (hA' v).2 ⟨u, huA, hvu⟩
    exact (hT v).mpr ⟨A', (hB A').mpr ⟨k', hk'w, (eval_fAt _ _ _ _).mpr hFk'A'⟩, hvA'⟩

private theorem every_set_in_V (hM : Model E) [Nonempty V] (x : V) :
    ∃ α v, Ordinal E α ∧ VVal E α v ∧ E x v := by
  obtain ⟨T, hxT, hTtrans⟩ := tc_exists hM x
  -- Bad(y) := ¬ ∃ α v, Ordinal α ∧ VVal α v ∧ y ∈ v
  let fNoV : Formula := fNot (.ex (.ex (.and (fOrdinal 1) (.and (fVVal 1 0) (.mem 2 0)))))
  have hNoVBd : Bound fNoV 1 := ⟨⟨bound_fOrdinal (by omega), bound_fVVal (by omega) (by omega), ⟨by omega, by omega⟩⟩, trivial⟩
  obtain ⟨D, hD⟩ := ax_sep hM 0 fNoV hNoVBd [] rfl T
  apply Classical.byContradiction
  intro hno
  have hDne : ∃ y, E y D := ⟨x, (hD x).mpr ⟨hxT, fun ⟨α, v, ho, hv, hxv⟩ =>
    hno ⟨α, v, ho, (eval_fVVal _ _ _).mp hv, hxv⟩⟩⟩
  obtain ⟨y, hyD, hmin⟩ := ax_found hM hDne
  obtain ⟨hyT, hnoY⟩ := (hD y).mp hyD
  -- Every z ∈ y has a least ordinal ρ(z) such that ∃ v, VVal ρ(z) v ∧ z ∈ v!
  -- Formula fLeastRank (0=z, 1=α): Ordinal α ∧ (∃ v, VVal α v ∧ z ∈ v) ∧ ∀ β ∈ α, ¬ ∃ v, VVal β v ∧ z ∈ v
  let fRank : Formula :=
    .and (fOrdinal 1) (.and (.ex (.and (fVVal 2 0) (.mem 1 0)))
      (.all (.imp (.mem 0 2) (fNot (.ex (.and (fVVal 1 0) (.mem 2 0)))))))
  have hRankBd : Bound fRank 2 :=
    ⟨bound_fOrdinal (by omega),
     ⟨bound_fVVal (by omega) (by omega), ⟨by omega, by omega⟩⟩,
     ⟨⟨by omega, by omega⟩, ⟨⟨bound_fVVal (by omega) (by omega), ⟨by omega, by omega⟩⟩, trivial⟩⟩⟩
  have hRankFunc : ∀ z α₁ α₂,
      eval E fRank (pushValue (pushValue (pushParams (fun _ => arbV) []) α₁) z) →
      eval E fRank (pushValue (pushValue (pushParams (fun _ => arbV) []) α₂) z) →
      α₁ = α₂ := by
    intro z α₁ α₂ ⟨ho₁, ⟨v₁, hv₁, hz₁⟩, hmin₁⟩ ⟨ho₂, ⟨v₂, hv₂, hz₂⟩, hmin₂⟩
    have hv₁' : VVal E α₁ v₁ := (eval_fVVal _ _ _).mp hv₁
    have hv₂' : VVal E α₂ v₂ := (eval_fVVal _ _ _).mp hv₂
    rcases ordinal_trichotomy hM ho₁ ho₂ with h1 | h2 | h3
    · exact False.elim (hmin₂ α₁ h1 ⟨v₁, (eval_fVVal _ _ _).mpr hv₁', hz₁⟩)
    · exact h2
    · exact False.elim (hmin₁ α₂ h3 ⟨v₂, (eval_fVVal _ _ _).mpr hv₂', hz₂⟩)
  -- Collect { succ α | ∃ z ∈ y, fRank z α } via Replacement on y!
  let fSuccRank : Formula := .ex (.and (fSucc 0 2)
    (.and (fOrdinal 0) (.and (.ex (.and (fVVal 1 0) (.mem 2 0)))
      (.all (.imp (.mem 0 1) (fNot (.ex (.and (fVVal 1 0) (.mem 3 0)))))))))
  have hSRBd : Bound fSuccRank 2 :=
    ⟨bound_fSucc (by omega) (by omega), bound_fOrdinal (by omega),
     ⟨bound_fVVal (by omega) (by omega), ⟨by omega, by omega⟩⟩,
     ⟨⟨by omega, by omega⟩, ⟨⟨bound_fVVal (by omega) (by omega), ⟨by omega, by omega⟩⟩, trivial⟩⟩⟩
  have hSRFunc : ∀ z s₁ s₂,
      eval E fSuccRank (pushValue (pushValue (pushParams (fun _ => arbV) []) s₁) z) →
      eval E fSuccRank (pushValue (pushValue (pushParams (fun _ => arbV) []) s₂) z) →
      s₁ = s₂ := by
    intro z s₁ s₂ ⟨α₁, hs₁, ho₁, ⟨v₁, hv₁, hz₁⟩, hm₁⟩ ⟨α₂, hs₂, ho₂, ⟨v₂, hv₂, hz₂⟩, hm₂⟩
    have hv₁' : VVal E α₁ v₁ := (eval_fVVal _ _ _).mp hv₁
    have hv₂' : VVal E α₂ v₂ := (eval_fVVal _ _ _).mp hv₂
    have hαeq : α₁ = α₂ := by
      rcases ordinal_trichotomy hM ho₁ ho₂ with h1 | h2 | h3
      · exact False.elim (hm₂ α₁ h1 ⟨v₁, (eval_fVVal _ _ _).mpr hv₁', hz₁⟩)
      · exact h2
      · exact False.elim (hm₁ α₂ h3 ⟨v₂, (eval_fVVal _ _ _).mpr hv₂', hz₂⟩)
    subst hαeq
    exact ax_ext hM (fun u => ((eval_fSucc _ _ _).mp hs₁ u).trans ((eval_fSucc _ _ _).mp hs₂ u).symm)
  obtain ⟨B, hB⟩ := ax_rep hM 0 fSuccRank hSRBd [] rfl hSRFunc y
  obtain ⟨U, hU⟩ := ax_union hM B
  have hUord : Ordinal E U := ordinal_union hM (fun s hs => by
    obtain ⟨z, _, α, hsα, ho, _, _⟩ := (hB s).mp hs
    exact ordinal_succ ho ((eval_fSucc _ _ _).mp hsα)) hU
  obtain ⟨U', hU'⟩ := succ_exists hM U
  have hU'ord : Ordinal E U' := ordinal_succ hUord hU'
  obtain ⟨vU, hvU⟩ := vval_exists hM hUord
  obtain ⟨vU', hvU'⟩ := vval_exists hM hU'ord
  have hySub : SubSet E y vU := by
    intro z hzy
    have hzT : E z T := hTtrans y hyT z hzy
    have hexZ : ∃ α v, Ordinal E α ∧ VVal E α v ∧ E z v := by
      apply Classical.byContradiction
      intro hnoZ
      exact hmin z hzy ((hD z).mpr ⟨hzT, fun ⟨α, v, ho, hv, hzv⟩ =>
        hnoZ ⟨α, v, ho, (eval_fVVal _ _ _).mp hv, hzv⟩⟩)
    obtain ⟨α0, v0, ho0, hv0, hzv0⟩ := hexZ
    obtain ⟨α0', hα0'⟩ := succ_exists hM α0
    let fHit : Formula := .ex (.and (fVVal 1 0) (.mem 2 0))
    have hHitBd : Bound fHit 2 := ⟨bound_fVVal (by omega) (by omega), ⟨by omega, by omega⟩⟩
    obtain ⟨H, hH⟩ := ax_sep hM 1 fHit hHitBd [z] rfl α0'
    obtain ⟨α, hαH, hminα⟩ := ax_found hM ⟨α0, (hH α0).mpr ⟨(hα0' α0).mpr (Or.inr rfl),
      v0, (eval_fVVal _ _ _).mpr hv0, hzv0⟩⟩
    obtain ⟨hαα0', v, hv', hzv⟩ := (hH α).mp hαH
    have hvV : VVal E α v := (eval_fVVal _ _ _).mp hv'
    have hαOrd : Ordinal E α := ordinal_elem (ordinal_succ ho0 hα0') hαα0'
    obtain ⟨α', hα'⟩ := succ_exists hM α
    have hα'B : E α' B := by
      refine (hB α').mpr ⟨z, hzy, α, (eval_fSucc 0 2 _).mpr hα', hαOrd,
        ⟨v, (eval_fVVal 1 0 _).mpr hvV, hzv⟩, ?_⟩
      intro β hβα ⟨w, hw', hzw⟩
      have hwV : VVal E β w := (eval_fVVal 1 0 _).mp hw'
      exact hminα β hβα ((hH β).mpr
        ⟨(ordinal_succ ho0 hα0').1 α hαα0' β hβα, w, (eval_fVVal 1 0 _).mpr hwV, hzw⟩)
    have hαU : E α U := (hU α).mpr ⟨α', hα'B, (hα' α).mpr (Or.inr rfl)⟩
    exact vval_mono hM hαU hvV hvU z hzv
  have hyIn : E y vU' := (vval_spec hM hvU' y).mpr ⟨U, (hU' U).mpr (Or.inr rfl), vU, hvU, hySub⟩
  exact hnoY ⟨U', vU', hU'ord, (eval_fVVal _ _ _).mpr hvU', hyIn⟩

/-! ### 8. Lemma 4.1: Definable Pointed Hulls in `(V, E)` -/

private theorem definable_pointed_hull (hM : Model E) [Nonempty V]
    (n : Nat) (fR : Formula) (hRBd : Bound fR (n + 2)) (ps : List V) (hlen : ps.length = n)
    (u0 v0 : V) :
    let R := fun u v => eval E fR (pushValue (pushValue (pushParams (fun _ => arbV) ps) u) v)
    ∃ C : V,
      (R u0 v0 → E v0 C) ∧
      ∀ z, E z C →
        (∃ p, R p z) ∧
        ∀ u, SubSet E u z → (∃ v, R u v) → ∃ w, E w C ∧ R u w := by
  intro R
  let sBase := pushParams (fun _ => arbV) ps
  -- 1. Scott's trick: for each u, S(u) = minimal-rank witnesses of R(u, ·) (or ∅ if none)
  -- Helper: fR shifted to arbitrary indices!
  -- Inside fScott (Bound n+2: 0=u, 1=S, 2+i=ps[i]):
  --   ((¬ ∃ v, R(u, v)) ∧ Empty S) ∨
  --   (∃ α Vα, Ordinal α ∧ VVal α Vα ∧ (∃ v ∈ Vα, R(u, v)) ∧
  --     (∀ β ∈ α, ¬ ∃ Vβ, VVal β Vβ ∧ ∃ v ∈ Vβ, R(u, v)) ∧
  --     (∀ v, v ∈ S ↔ v ∈ Vα ∧ R(u, v)))
  -- Let's write tiny rename maps for fR (0=v, 1=u, 2+i=ps[i]):
  let mapR (vi ui shift : Nat) : Nat → Nat
    | 0 => vi
    | 1 => ui
    | j + 2 => j + shift
  have bdR : ∀ vi ui sh m, vi < m → ui < m → n + sh ≤ m → Bound (rename (mapR vi ui sh) fR) m := by
    intro vi ui sh m h1 h2 h3
    apply bound_rename fR (n + 2) m (mapR vi ui sh) hRBd
    intro i hi
    cases i with
    | zero => exact h1
    | succ k => cases k with | zero => exact h2 | succ j => simp [mapR]; omega
  -- fScott (0=u, 1=S, 2+i=ps[i]):
  let fNoWit : Formula := fNot (.ex (rename (mapR 0 1 3) fR))
  let fHasInV (uIdx vIdx sh : Nat) : Formula := .ex (.and (.mem 0 (vIdx + 1)) (rename (mapR 0 (uIdx + 1) (sh + 1)) fR))
  let fScott : Formula :=
    .or (.and fNoWit (fEmpty 1))
        (.ex (.ex (.and (fOrdinal 1) (.and (fVVal 1 0)
          (.and (fHasInV 2 0 4)
            (.and (.all (.imp (.mem 0 2) (fNot (.ex (.and (fVVal 1 0) (fHasInV 4 0 6))))))
              (.all (fIff (.mem 0 4) (.and (.mem 0 1) (rename (mapR 0 3 5) fR))))))))))
  have hScottBd : Bound fScott (n + 2) := by
    refine ⟨⟨⟨bdR 0 1 3 (n + 3) (by omega) (by omega) (by omega), trivial⟩, bound_fEmpty (by omega)⟩,
      bound_fOrdinal (by omega), bound_fVVal (by omega) (by omega),
      ⟨⟨by omega, by omega⟩, bdR 0 3 5 (n + 5) (by omega) (by omega) (by omega)⟩,
      ⟨⟨⟨by omega, by omega⟩, ⟨⟨bound_fVVal (by omega) (by omega),
        ⟨⟨by omega, by omega⟩, bdR 0 5 7 (n + 7) (by omega) (by omega) (by omega)⟩⟩, trivial⟩⟩,
       ⟨⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, bdR 0 3 5 (n + 5) (by omega) (by omega) (by omega)⟩⟩,
        ⟨⟨⟨by omega, by omega⟩, bdR 0 3 5 (n + 5) (by omega) (by omega) (by omega)⟩, ⟨by omega, by omega⟩⟩⟩⟩⟩
  have hScottEval : ∀ u S,
      eval E fScott (pushValue (pushValue sBase S) u) ↔
        ((¬ ∃ v, R u v) ∧ Empty E S) ∨
        (∃ α Vα, Ordinal E α ∧ VVal E α Vα ∧ (∃ v, E v Vα ∧ R u v) ∧
          (∀ β, E β α → ¬ ∃ Vβ, VVal E β Vβ ∧ ∃ v, E v Vβ ∧ R u v) ∧
          (∀ v, E v S ↔ E v Vα ∧ R u v)) := by
    intro u S
    have hR1 : ∀ v, eval E (rename (mapR 0 1 3) fR) (pushValue (pushValue (pushValue sBase S) u) v) ↔ R u v := by
      intro v; rw [eval_rename]
      have hfn : (fun i => pushValue (pushValue (pushValue sBase S) u) v (mapR 0 1 3 i)) = pushValue (pushValue sBase u) v := by
        funext i; cases i with | zero => rfl | succ k => cases k with | zero => rfl | succ j => rfl
      rw [hfn]
    have hR2 : ∀ α Vα v, eval E (rename (mapR 0 3 5) fR)
        (pushValue (pushValue (pushValue (pushValue (pushValue sBase S) u) α) Vα) v) ↔ R u v := by
      intro α Vα v; rw [eval_rename]
      have hfn : (fun i => pushValue (pushValue (pushValue (pushValue (pushValue sBase S) u) α) Vα) v (mapR 0 3 5 i)) =
          pushValue (pushValue sBase u) v := by
        funext i; cases i with | zero => rfl | succ k => cases k with | zero => rfl | succ j => rfl
      rw [hfn]
    have hR3 : ∀ α Vα β Vβ v, eval E (rename (mapR 0 5 7) fR)
        (pushValue (pushValue (pushValue (pushValue (pushValue (pushValue (pushValue sBase S) u) α) Vα) β) Vβ) v) ↔ R u v := by
      intro α Vα β Vβ v; rw [eval_rename]
      have hfn : (fun i => pushValue (pushValue (pushValue (pushValue (pushValue (pushValue (pushValue sBase S) u) α) Vα) β) Vβ) v (mapR 0 5 7 i)) =
          pushValue (pushValue sBase u) v := by
        funext i; cases i with | zero => rfl | succ k => cases k with | zero => rfl | succ j => rfl
      rw [hfn]
    constructor
    · intro h
      rcases h with h0 | ⟨α, Vα, ho, hv, ⟨v, hvV, hRv⟩, hmin, hmem⟩
      · exact Or.inl ⟨fun ⟨v, hv⟩ => h0.1 ⟨v, (hR1 v).mpr hv⟩, h0.2⟩
      · refine Or.inr ⟨α, Vα, ho, (eval_fVVal _ _ _).mp hv, ⟨v, hvV, (hR2 α Vα v).mp hRv⟩,
          fun β hβ ⟨Vβ, hVβ, w, hwV, hRw⟩ => hmin β hβ ⟨Vβ, (eval_fVVal _ _ _).mpr hVβ, w, hwV, (hR3 α Vα β Vβ w).mpr hRw⟩,
          fun w => ⟨fun hwS => let ⟨h1, h2⟩ := (hmem w).1 hwS; ⟨h1, (hR2 α Vα w).mp h2⟩,
                    fun ⟨h1, h2⟩ => (hmem w).2 ⟨h1, (hR2 α Vα w).mpr h2⟩⟩⟩
    · intro h
      rcases h with h0 | ⟨α, Vα, ho, hv, ⟨v, hvV, hRv⟩, hmin, hmem⟩
      · exact Or.inl ⟨fun ⟨v, hv⟩ => h0.1 ⟨v, (hR1 v).mp hv⟩, h0.2⟩
      · refine Or.inr ⟨α, Vα, ho, (eval_fVVal _ _ _).mpr hv, ⟨v, hvV, (hR2 α Vα v).mpr hRv⟩,
          fun β hβ ⟨Vβ, hVβ, w, hwV, hRw⟩ => hmin β hβ ⟨Vβ, (eval_fVVal _ _ _).mp hVβ, w, hwV, (hR3 α Vα β Vβ w).mp hRw⟩,
          fun w => ⟨fun hwS => let ⟨h1, h2⟩ := (hmem w).mp hwS; ⟨h1, (hR2 α Vα w).mpr h2⟩,
                    fun ⟨h1, h2⟩ => (hmem w).mpr ⟨h1, (hR2 α Vα w).mp h2⟩⟩⟩
  have hScottTotal : ∀ u, ∃ S, eval E fScott (pushValue (pushValue sBase S) u) := by
    intro u
    by_cases hex : ∃ v, R u v
    · obtain ⟨v1, hRv1⟩ := hex
      obtain ⟨α0, V0, ho0, hV0, hv1V0⟩ := every_set_in_V hM v1
      obtain ⟨α0', hα0'⟩ := succ_exists hM α0
      -- Minimal α ∈ α0' with ∃ Vα, VVal α Vα ∧ ∃ v ∈ Vα, R u v
      let fHitU : Formula := .ex (.and (fVVal 1 0) (.ex (.and (.mem 0 1) (rename (mapR 0 3 4) fR))))
      have hHitUBd : Bound fHitU (n + 2) :=
        ⟨bound_fVVal (by omega) (by omega), ⟨⟨by omega, by omega⟩, bdR 0 3 4 (n + 4) (by omega) (by omega) (by omega)⟩⟩
      obtain ⟨H, hH⟩ := ax_sep hM (n + 1) fHitU hHitUBd (ps ++ [u]) (by simp [hlen]) α0'
      have hHitEval : ∀ α, eval E fHitU (pushValue (pushParams (fun _ => arbV) (ps ++ [u])) α) ↔
          ∃ Vα, VVal E α Vα ∧ ∃ v, E v Vα ∧ R u v := by
        intro α
        have hR4 : ∀ Vα v, eval E (rename (mapR 0 3 4) fR)
            (pushValue (pushValue (pushValue (pushParams (fun _ => arbV) (ps ++ [u])) α) Vα) v) ↔ R u v := by
          intro Vα v; rw [pushParams_append, eval_rename]
          have hfn : (fun i => pushValue (pushValue (pushValue (pushParams sBase [u]) α) Vα) v (mapR 0 3 4 i)) =
              pushValue (pushValue sBase u) v := by
            funext i; cases i with | zero => rfl | succ k => cases k with | zero => rfl | succ j => rfl
          rw [hfn]
        constructor
        · rintro ⟨Vα, hVα, v, hvV, hRv⟩; exact ⟨Vα, (eval_fVVal _ _ _).mp hVα, v, hvV, (hR4 Vα v).mp hRv⟩
        · rintro ⟨Vα, hVα, v, hvV, hRv⟩; exact ⟨Vα, (eval_fVVal _ _ _).mpr hVα, v, hvV, (hR4 Vα v).mpr hRv⟩
      obtain ⟨α, hαH, hminα⟩ := ax_found hM ⟨α0, (hH α0).mpr ⟨(hα0' α0).mpr (Or.inr rfl),
        (hHitEval α0).mpr ⟨V0, hV0, v1, hv1V0, hRv1⟩⟩⟩
      obtain ⟨hαα0', hHitα⟩ := (hH α).mp hαH
      obtain ⟨Vα, hVα, v2, hv2V, hRv2⟩ := (hHitEval α).mp hHitα
      have hαOrd : Ordinal E α := ordinal_elem (ordinal_succ ho0 hα0') hαα0'
      -- S := { v ∈ Vα | R u v } by Separation!
      obtain ⟨S, hS⟩ := ax_sep hM (n + 1) fR hRBd (ps ++ [u]) (by simp [hlen]) Vα
      have hS' : ∀ v, E v S ↔ E v Vα ∧ R u v := by
        intro v; simpa [pushParams_append, pushParams, R, sBase] using hS v
      refine ⟨S, (hScottEval u S).mpr (Or.inr ⟨α, Vα, hαOrd, hVα, ⟨v2, hv2V, hRv2⟩, ?_, hS'⟩)⟩
      intro β hβα hHitβ
      exact hminα β hβα ((hH β).mpr ⟨(ordinal_succ ho0 hα0').1 α hαα0' β hβα, (hHitEval β).mpr hHitβ⟩)
    · obtain ⟨z, hz⟩ := ax_empty hM
      exact ⟨z, (hScottEval u z).mpr (Or.inl ⟨hex, hz⟩)⟩
  have hScottFunc : ∀ u S₁ S₂,
      eval E fScott (pushValue (pushValue sBase S₁) u) →
      eval E fScott (pushValue (pushValue sBase S₂) u) → S₁ = S₂ := by
    intro u S₁ S₂ h1 h2
    rcases (hScottEval u S₁).mp h1 with ⟨hno, hz₁⟩ | ⟨α₁, V₁, ho₁, hV₁, hex₁, hmin₁, hS₁⟩
    · rcases (hScottEval u S₂).mp h2 with ⟨_, hz₂⟩ | ⟨_, _, _, _, ⟨v, _, hRv⟩, _, _⟩
      · exact ax_ext hM (fun x => ⟨fun h => False.elim (hz₁ x h), fun h => False.elim (hz₂ x h)⟩)
      · exact False.elim (hno ⟨v, hRv⟩)
    · rcases (hScottEval u S₂).mp h2 with ⟨hno, _⟩ | ⟨α₂, V₂, ho₂, hV₂, hex₂, hmin₂, hS₂⟩
      · rcases hex₁ with ⟨v, _, hRv⟩; exact False.elim (hno ⟨v, hRv⟩)
      · have hαeq : α₁ = α₂ := by
          rcases ordinal_trichotomy hM ho₁ ho₂ with hlt | heq | hgt
          · exact False.elim (hmin₂ α₁ hlt ⟨V₁, hV₁, hex₁⟩)
          · exact heq
          · exact False.elim (hmin₁ α₂ hgt ⟨V₂, hV₂, hex₂⟩)
        subst hαeq
        have hVeq : V₁ = V₂ := vval_unique hM hV₁ hV₂
        subst hVeq
        exact ax_ext hM (fun v => (hS₁ v).trans (hS₂ v).symm)
  -- 2. Define Step(X, Y): Y = X ∪ ⋃ { S(u) | ∃ z ∈ X, u ⊆ z }
  -- Formula fHullStep (0=X, 1=Y, 2+i=ps[i]):
  --   ∀ w, w ∈ Y ↔ w ∈ X ∨ ∃ z ∈ X, ∃ u, u ⊆ z ∧ ∃ S, Scott(u, S) ∧ w ∈ S
  -- Under ∀ w (0), ∃ z (0), ∃ u (0), ∃ S (0): S=0, u=1, z=2, w=3, X=4, Y=5, ps[i]=6+i!
  let mapSc : Nat → Nat | 0 => 1 | 1 => 0 | j + 2 => j + 6
  let fHullStep : Formula :=
    .all (fIff (.mem 0 2)
      (.or (.mem 0 1)
        (.ex (.and (.mem 0 2)
          (.ex (.and (fSub 0 1)
            (.ex (.and (rename mapSc fScott) (.mem 3 0)))))))))
  have hHullStepBd : Bound fHullStep (n + 2) := by
    have hsc : Bound (rename mapSc fScott) (n + 6) := by
      apply bound_rename fScott (n + 2) (n + 6) mapSc hScottBd
      intro i hi; cases i with | zero => simp [mapSc] | succ k => cases k with | zero => simp [mapSc] | succ j => simp [mapSc]; omega
    refine ⟨⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, ⟨bound_fSub (by omega) (by omega), ⟨hsc, ⟨by omega, by omega⟩⟩⟩⟩⟩⟩,
            ⟨⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, ⟨bound_fSub (by omega) (by omega), ⟨hsc, ⟨by omega, by omega⟩⟩⟩⟩⟩, ⟨by omega, by omega⟩⟩⟩
  have hHullStepEval : ∀ X Y,
      eval E fHullStep (pushValue (pushValue sBase Y) X) ↔
        ∀ w, E w Y ↔ E w X ∨ ∃ z, E z X ∧ ∃ u, SubSet E u z ∧ ∃ S,
          eval E fScott (pushValue (pushValue sBase S) u) ∧ E w S := by
    intro X Y
    have hsc : ∀ w z u S,
        eval E (rename mapSc fScott) (pushValue (pushValue (pushValue (pushValue (pushValue (pushValue sBase Y) X) w) z) u) S) ↔
        eval E fScott (pushValue (pushValue sBase S) u) := by
      intro w z u S; rw [eval_rename]
      have hfn : (fun i => pushValue (pushValue (pushValue (pushValue (pushValue (pushValue sBase Y) X) w) z) u) S (mapSc i)) =
          pushValue (pushValue sBase S) u := by
        funext i; cases i with | zero => rfl | succ k => cases k with | zero => rfl | succ j => rfl
      rw [hfn]
    constructor
    · intro h w
      constructor
      · intro hwY
        rcases (h w).1 hwY with h1 | ⟨z, hz, u, hsub, S, hS, hwS⟩
        · exact Or.inl h1
        · exact Or.inr ⟨z, hz, u, hsub, S, (hsc w z u S).mp hS, hwS⟩
      · intro hw
        apply (h w).2
        rcases hw with h1 | ⟨z, hz, u, hsub, S, hS, hwS⟩
        · exact Or.inl h1
        · exact Or.inr ⟨z, hz, u, hsub, S, (hsc w z u S).mpr hS, hwS⟩
    · intro h w
      constructor
      · intro hwY
        rcases (h w).mp hwY with h1 | ⟨z, hz, u, hsub, S, hS, hwS⟩
        · exact Or.inl h1
        · exact Or.inr ⟨z, hz, u, hsub, S, (hsc w z u S).mpr hS, hwS⟩
      · intro hw
        apply (h w).mpr
        rcases hw with h1 | ⟨z, hz, u, hsub, S, hS, hwS⟩
        · exact Or.inl h1
        · exact Or.inr ⟨z, hz, u, hsub, S, (hsc w z u S).mp hS, hwS⟩
  have hHullStepTotal : ∀ X, ∃ Y, eval E fHullStep (pushValue (pushValue sBase Y) X) := by
    intro X
    -- First collect P_all = ⋃_{z ∈ X} P(z) by Replacement + Union!
    let fPowEq : Formula := .all (fIff (.mem 0 2) (fSub 0 1))
    have hPowEqBd : Bound fPowEq 2 :=
      ⟨⟨⟨by omega, by omega⟩, bound_fSub (by omega) (by omega)⟩,
       ⟨bound_fSub (by omega) (by omega), ⟨by omega, by omega⟩⟩⟩
    obtain ⟨Ps, hPs⟩ := ax_rep hM 0 fPowEq hPowEqBd [] rfl
      (fun z P₁ P₂ h1 h2 => ax_ext hM (fun u => ⟨fun h => (h2 u).2 ((h1 u).1 h), fun h => (h1 u).2 ((h2 u).1 h)⟩)) X
    obtain ⟨U_sub, hU_sub⟩ := ax_union hM Ps
    -- Now collect { S(u) | u ∈ U_sub } by Replacement with fScott!
    obtain ⟨Ss, hSs⟩ := ax_rep hM n fScott hScottBd ps hlen hScottFunc U_sub
    obtain ⟨U_S, hU_S⟩ := ax_union hM Ss
    obtain ⟨Y, hY⟩ := binUnion_exists hM X U_S
    refine ⟨Y, (hHullStepEval X Y).mpr (fun w => ?_)⟩
    rw [hY, hU_S]
    constructor
    · intro hw
      rcases hw with h | ⟨S, hSSs, hwS⟩
      · exact Or.inl h
      · obtain ⟨u, huU, hSu⟩ := (hSs S).mp hSSs
        obtain ⟨P, hPPs, huP⟩ := (hU_sub u).mp huU
        obtain ⟨z, hzX, hPz⟩ := (hPs P).mp hPPs
        exact Or.inr ⟨z, hzX, u, (hPz u).1 huP, S, hSu, hwS⟩
    · intro hw
      rcases hw with h | ⟨z, hzX, u, hsub, S, hSu, hwS⟩
      · exact Or.inl h
      · obtain ⟨P, hP⟩ := ax_power hM z
        have hPPs : E P Ps := (hPs P).mpr ⟨z, hzX, fun t => ⟨(hP t).mp, (hP t).mpr⟩⟩
        have huU : E u U_sub := (hU_sub u).mpr ⟨P, hPPs, (hP u).mpr hsub⟩
        exact Or.inr ⟨S, (hSs S).mpr ⟨u, huU, hSu⟩, hwS⟩
  have hHullStepFunc : ∀ X Y₁ Y₂,
      eval E fHullStep (pushValue (pushValue sBase Y₁) X) →
      eval E fHullStep (pushValue (pushValue sBase Y₂) X) → Y₁ = Y₂ := by
    intro X Y₁ Y₂ h1 h2
    exact ax_ext hM (fun w => ((hHullStepEval X Y₁).mp h1 w).trans ((hHullStepEval X Y₂).mp h2 w).symm)
  -- 3. C₀ = { v ∈ {v0} | R u0 v }
  obtain ⟨sv0, hsv0⟩ := ax_pair hM v0 v0
  obtain ⟨C0, hC0_raw⟩ := ax_sep hM (n + 1) fR hRBd (ps ++ [u0]) (by simp [hlen]) sv0
  have hC0 : ∀ v, E v C0 ↔ E v sv0 ∧ R u0 v := by
    intro v; simpa [pushParams_append, pushParams, R, sBase] using hC0_raw v
  -- 4. ω-recursion starting from C0!
  obtain ⟨w, hw⟩ := ax_omega hM
  obtain ⟨F, hFun, hF0, hFstep⟩ := omega_recursion hM hw n fHullStep hHullStepBd ps hlen
    hHullStepTotal hHullStepFunc C0
  -- Collect range of F on w and take union C = ⋃_{k ∈ w} F(k)!
  obtain ⟨RangeF, hRangeF⟩ := ax_rep hM 1 (fAt 2 0 1) (bound_fAt (by omega) (by omega) (by omega)) [F] rfl
    (fun k y₁ y₂ h1 h2 => by
      have h1' : At E F k y₁ := (eval_fAt _ _ _ _).mp h1
      have h2' : At E F k y₂ := (eval_fAt _ _ _ _).mp h2
      have hkw : E k w := by
        obtain ⟨q, hqf, hqp⟩ := h1'; obtain ⟨x', _, hx'w, hqp'⟩ := hFun.2 q hqf
        rwa [(orderedPair_inj hM hqp hqp').1]
      obtain ⟨_, _, hu⟩ := hFun.1 k hkw
      exact (hu y₁ h1').trans (hu y₂ h2').symm) w
  obtain ⟨C, hC⟩ := ax_union hM RangeF
  -- Prove by omega_induction that ∀ k ∈ w, ∀ X, At F k X → ∀ z ∈ X, ∃ p, R p z!
  -- Formula fAllWit (0=k, 1=F, 2+i=ps[i]):
  --   ∀ X, At F k X → ∀ z ∈ X, ∃ p, R(p, z)
  let fAllWit : Formula :=
    .all (.imp (fAt 2 1 0) (.all (.imp (.mem 0 1) (.ex (rename (mapR 1 0 5) fR)))))
  have hAllWitBd : Bound fAllWit (n + 2) :=
    ⟨bound_fAt (by omega) (by omega) (by omega),
     ⟨⟨by omega, by omega⟩, bdR 1 0 5 (n + 5) (by omega) (by omega) (by omega)⟩⟩
  have hAllWit : ∀ k, E k w → ∀ X, At E F k X → ∀ z, E z X → ∃ p, R p z := by
    have hR5 : ∀ k X z p,
        eval E (rename (mapR 1 0 5) fR) (pushValue (pushValue (pushValue (pushValue (pushParams (fun _ => arbV) (ps ++ [F])) k) X) z) p) ↔
        R p z := by
      intro k X z p; rw [pushParams_append, eval_rename]
      have hfn : (fun i => pushValue (pushValue (pushValue (pushValue (pushParams sBase [F]) k) X) z) p (mapR 1 0 5 i)) =
          pushValue (pushValue sBase p) z := by
        funext i; cases i with | zero => rfl | succ a => cases a with | zero => rfl | succ j => rfl
      rw [hfn]
    have hInd := omega_induction hM hw (n + 1) fAllWit hAllWitBd (ps ++ [F]) (by simp [hlen])
      (fun z hz X hFX' y hyX => by
        rw [pushParams_append] at hFX'
        have hFX : At E F z X := (eval_fAt _ _ _ _).mp hFX'
        obtain ⟨z', hz', hz'w⟩ := hw.1.1
        have hzeq : z = z' := ax_ext hM (fun u => ⟨fun h => False.elim (hz u h), fun h => False.elim (hz' u h)⟩)
        subst hzeq
        obtain ⟨_, _, hu⟩ := hFun.1 z hz'w
        have hXC0 : X = C0 := (hu X hFX).trans (hu C0 (hF0 z hz)).symm
        subst X
        exact ⟨u0, (hR5 z C0 y u0).mpr ((hC0 y).mp hyX).2⟩)
      (fun k k' hkw hkk' ih Y hFY' y hyY => by
        rw [pushParams_append] at hFY'
        have hFY : At E F k' Y := (eval_fAt _ _ _ _).mp hFY'
        obtain ⟨X, hFX, _⟩ := hFun.1 k hkw
        have hSt := (hHullStepEval X Y).mp (hFstep k k' hkw hkk' X Y hFX hFY) y
        rcases hSt.mp hyY with hyX | ⟨_, _, u, _, S, hSu, hyS⟩
        · have hFX' : eval E (fAt 2 1 0) (pushValue (pushValue (pushParams (fun _ => arbV) (ps ++ [F])) k) X) := by
            rw [pushParams_append]; exact (eval_fAt _ _ _ _).mpr hFX
          obtain ⟨p, hp⟩ := ih X hFX' y hyX
          exact ⟨p, (hR5 k' Y y p).mpr ((hR5 k X y p).mp hp)⟩
        · rcases (hScottEval u S).mp hSu with ⟨_, hzS⟩ | ⟨_, _, _, _, _, _, hSmem⟩
          · exact False.elim (hzS y hyS)
          · exact ⟨u, (hR5 k' Y y u).mpr ((hSmem y).mp hyS).2⟩)
    intro k hkw X hFX z hzX
    have hFX' : eval E (fAt 2 1 0) (pushValue (pushValue (pushParams (fun _ => arbV) (ps ++ [F])) k) X) := by
      rw [pushParams_append]; exact (eval_fAt _ _ _ _).mpr hFX
    obtain ⟨p, hp⟩ := hInd k hkw X hFX' z hzX
    exact ⟨p, (hR5 k X z p).mp hp⟩
  -- 5. Verify the pointed hull properties for C!
  refine ⟨C, ?_, ?_⟩
  · intro hR0
    obtain ⟨z, hz, hzw⟩ := hw.1.1
    have hv0C0 : E v0 C0 := (hC0 v0).mpr ⟨(hsv0 v0).mpr (Or.inl rfl), hR0⟩
    exact (hC v0).mpr ⟨C0, (hRangeF C0).mpr ⟨z, hzw, (eval_fAt _ _ _ _).mpr (hF0 z hz)⟩, hv0C0⟩
  · intro z hzC
    obtain ⟨X, hXR, hzX⟩ := (hC z).mp hzC
    obtain ⟨k, hkw, hFX'⟩ := (hRangeF X).mp hXR
    have hFX : At E F k X := (eval_fAt _ _ _ _).mp hFX'
    refine ⟨hAllWit k hkw X hFX z hzX, fun u hsub ⟨v, hRuv⟩ => ?_⟩
    obtain ⟨k', hkk', hk'w⟩ := hw.1.2 k hkw
    obtain ⟨Y, hFY, _⟩ := hFun.1 k' hk'w
    obtain ⟨S, hSu⟩ := hScottTotal u
    rcases (hScottEval u S).mp hSu with ⟨hno, _⟩ | ⟨_, _, _, _, ⟨v', hv'V, hRv'⟩, _, hSmem⟩
    · exact False.elim (hno ⟨v, hRuv⟩)
    · have hv'S : E v' S := (hSmem v').mpr ⟨hv'V, hRv'⟩
      have hv'Y : E v' Y := ((hHullStepEval X Y).mp (hFstep k k' hkw hkk' X Y hFX hFY) v').mpr
        (Or.inr ⟨z, hzX, u, hsub, S, hSu, hv'S⟩)
      have hv'C : E v' C := (hC v').mpr ⟨Y, (hRangeF Y).mpr ⟨k', hk'w, (eval_fAt _ _ _ _).mpr hFY⟩, hv'Y⟩
      exact ⟨v', hv'C, hRv'⟩

/-! ### 9. Soundness of Calculus C in Every ZF Model -/

private theorem evalC_Nc (hM : Model E) [Nonempty V] (B : Nat) (env : Nat → V) :
    evalC E (Nc B) env ↔ ¬ evalC E B env := by
  unfold Nc
  rw [evalC_Ic, evalC_one]
  exact ⟨fun h hB => mem_irrefl hM (env 0) (h hB), fun h hB => False.elim (h hB)⟩

private theorem upd_self {V : Type} (env : Nat → V) (k : Nat) (v₁ v₂ : V) :
    upd (upd env k v₁) k v₂ = upd env k v₂ := by
  funext i; unfold upd; split <;> rfl

private theorem upd_id {V : Type} (env : Nat → V) (k : Nat) :
    upd env k (env k) = env := by
  funext i; unfold upd; split
  · rename_i h; subst h; rfl
  · rfl

private theorem upd_comm {V : Type} (env : Nat → V) {k₁ k₂ : Nat} (hne : k₁ ≠ k₂) (v₁ v₂ : V) :
    upd (upd env k₁ v₁) k₂ v₂ = upd (upd env k₂ v₂) k₁ v₁ := by
  funext i; unfold upd
  by_cases h1 : i = k₂
  · subst h1; simp [hne.symm]
  · simp [h1]

private theorem evalC_upd_ge {V : Type} (E : V → V → Prop) {c k : Nat} (hge : c ≤ k)
    (env : Nat → V) (v : V) :
    evalC E c (upd env k v) ↔ evalC E c env := by
  apply evalC_congr
  intro i hi
  unfold upd
  have hne : i ≠ k := by omega
  simp [hne]

private def envParams {V : Type} (env : Nat → V) : Nat → List V
  | 0 => []
  | m + 1 => env m :: envParams env m

private theorem envParams_length {V : Type} (env : Nat → V) : ∀ m, (envParams env m).length = m
  | 0 => rfl
  | m + 1 => congrArg Nat.succ (envParams_length env m)

private theorem pushParams_ge {V : Type} :
    ∀ (xs : List V) (s : Nat → V) (k : Nat), pushParams s xs (xs.length + k) = s k
  | [], _, _ => by simp [pushParams]
  | x :: xs, s, k => by
    change pushParams (pushValue s x) xs (xs.length + 1 + k) = s k
    have : xs.length + 1 + k = xs.length + (k + 1) := by omega
    rw [this, pushParams_ge xs (pushValue s x) (k + 1)]
    rfl

private theorem pushParams_envParams_exact {V : Type} (s0 env : Nat → V) :
    ∀ (m i : Nat), i < m → pushParams s0 (envParams env m) i = env i
  | m + 1, i, hi => by
    change pushParams (pushValue s0 (env m)) (envParams env m) i = env i
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with
    | inl hlt => exact pushParams_envParams_exact (pushValue s0 (env m)) env m i hlt
    | inr heq =>
      rw [heq]
      have h := pushParams_ge (envParams env m) (pushValue s0 (env m)) 0
      rw [envParams_length] at h
      simpa [pushValue] using h

theorem provC_sound (hM : Model E) [Nonempty V] {p : Nat} (hP : ProvC p) :
    ∀ env : Nat → V, evalC E p env := by
  induction hP with
  | truth => intro _; simp [evalC]
  | mp _ _ ih1 ih2 =>
    intro env
    exact (evalC_Ic E _ _ env).mp (ih1 env) (ih2 env)
  | gen a _ ih =>
    intro env
    rw [evalC_Uc]
    intro v
    exact ih (upd env a v)
  | ax_rho8 a b c u =>
    intro env
    rw [rho8, evalC_Ic, evalC_Ic, evalC_Ic, evalC_Ic, evalC_Ic, evalC_Ic]
    intro h1 h2 _
    cases Classical.em (evalC E c env) with
    | inl hc => exact hc
    | inr hnc => exact h2 (h1 (fun hc => False.elim (hnc hc)))
  | ax_h1 x y =>
    intro env
    rw [head1, evalC_Ic, evalC_Nc hM, evalC_Uc]
    intro h
    apply Classical.byContradiction
    intro hnx
    apply h
    intro v
    rw [evalC_Nc hM, evalC_Uc]
    intro hv
    have h0 := hv (env y)
    rw [upd_self, upd_id] at h0
    exact hnx h0
  | ax_h2 x y z =>
    intro env
    rw [head2, evalC_Ic, evalC_Uc, evalC_Uc]
    intro h v1
    rw [evalC_Uc]
    intro v2
    by_cases hyz : y = z
    · subst hyz
      have h' := (evalC_Uc E y x (upd env y v2)).mp (h v2) v2
      simpa [upd_self] using h'
    · have h' := (evalC_Uc E z x (upd env y v2)).mp (h v2) v1
      rwa [upd_comm env (Ne.symm hyz)]
  | ax_h3 x y z =>
    intro env
    rw [head3, evalC_Ic, evalC_Mc, evalC_Ic, evalC_Ec, evalC_Mc]
    intro h1 h2; rwa [← h2]
  | ax_h4 x y z =>
    intro env
    rw [head4, evalC_Ic, evalC_Ec, evalC_Ic, evalC_Mc, evalC_Mc]
    intro h1 h2; rwa [← h1]
  | ax_h5 x y =>
    intro env
    rw [head5, evalC_Nc hM, evalC_Uc]
    intro h
    have hv := h (env x)
    rw [evalC_Nc hM, evalC_Ec] at hv
    apply hv
    unfold upd
    by_cases hxy : x = y
    · subst hxy; simp
    · simp [hxy]
  | ax_h6 x y z =>
    intro env
    rw [head6, evalC_Ic, evalC_Uc, evalC_Ic, evalC_Uc, evalC_Uc]
    intro h1 h2 v
    exact (evalC_Ic E z x _).mp (h2 v) (h1 v)
  | ax_gate a b c hca hcb =>
    intro env
    rw [gateF, evalC_Nc hM]
    intro hGate
    have hDelta : evalC E (Ic (Ec a b) (Uc c (Ec a b))) env := by
      rw [evalC_Ic, evalC_Ec, evalC_Uc]
      intro hab v
      rw [evalC_Ec]
      unfold upd
      simp [Ne.symm hca, Ne.symm hcb, hab]
    have hVax : evalC E (Ic (Mc a b) (Uc c (Mc a b))) env := by
      rw [evalC_Ic, evalC_Mc, evalC_Uc]
      intro hab v
      rw [evalC_Mc]
      unfold upd
      simp [Ne.symm hca, Ne.symm hcb, hab]
    have hQ : ∀ C : V, evalC E (gateG a b c) (upd env c C) :=
      (evalC_Uc E c _ env).mp ((evalC_Ic E _ _ env).mp ((evalC_Ic E _ _ env).mp hGate hDelta) hVax)
    -- Helper to simplify gateG at any C : V
    have hGateContra : ∀ C : V,
        (evalC E c env → E (env a) C) →
        (∀ z : V, E z C →
          ∃ p : V, evalC E c (upd (upd env a z) b p) ∧
            ∀ u : V, SubSet E u (if a = b then u else z) →
              ∀ v : V, evalC E c (upd (upd env b u) a v) →
                ∃ w : V, evalC E c (upd (upd env b u) a w) ∧ E w C) →
        False := by
      intro C hPt hCl
      have hG := hQ C
      rw [gateG, evalC_Ic] at hG
      have hLhs : evalC E (Uc a (Ic (Mc a c)
          (Nc (Uc b (Ic c (Nc (Uc b (Ic (Uc c (Ic (Mc c b) (Mc c a)))
            (Uc a (Ic c (Nc (Uc a (Ic c (Nc (Mc a c))))))))))))))) (upd env c C) := by
        rw [evalC_Uc]
        intro z
        rw [evalC_Ic, evalC_Mc]
        have hza : upd (upd env c C) a z a = z := by simp [upd]
        have hzc : upd (upd env c C) a z c = C := by simp [upd, hca]
        rw [hza, hzc]
        intro hzC
        obtain ⟨p, hpR, hpSub⟩ := hCl z hzC
        rw [evalC_Nc hM, evalC_Uc]
        intro hallP
        have hp1 := hallP p
        rw [evalC_Ic] at hp1
        have hpC : evalC E c (upd (upd (upd env c C) a z) b p) := by
          rw [upd_comm env hca, upd_comm (upd env a z) hcb, evalC_upd_ge E (Nat.le_refl c)]
          exact hpR
        have hp2 := hp1 hpC
        rw [evalC_Nc hM, evalC_Uc] at hp2
        apply hp2
        intro u
        rw [evalC_Ic, evalC_Uc]
        intro hSubBA
        have hSub : SubSet E u (if a = b then u else z) := by
          intro x hxu
          have hx := hSubBA x
          rw [evalC_Ic, evalC_Mc, evalC_Mc] at hx
          have hxb : upd (upd (upd (upd (upd env c C) a z) b p) b u) c x b = u := by
            simp [upd, Ne.symm hcb]
          have hxc : upd (upd (upd (upd (upd env c C) a z) b p) b u) c x c = x := by
            simp [upd]
          have hxa : upd (upd (upd (upd (upd env c C) a z) b p) b u) c x a = (if a = b then u else z) := by
            by_cases hab : a = b
            · subst hab; simp [upd, Ne.symm hca]
            · simp [upd, hab, Ne.symm hca]
          rw [hxc, hxb, hxa] at hx
          exact hx hxu
        rw [evalC_Uc]
        intro v
        rw [evalC_Ic]
        intro hvC
        have hvR : evalC E c (upd (upd env b u) a v) := by
          rw [upd_self] at hvC
          have h1 : upd (upd (upd (upd env c C) a z) b u) a v = upd (upd (upd env b u) a v) c C := by
            funext i; unfold upd
            by_cases hi1 : i = c
            · subst hi1; simp [hca, hcb]
            · by_cases hi2 : i = a
              · subst hi2; simp [hi1]
              · by_cases hi3 : i = b
                · subst hi3; simp [hi1, hi2]
                · simp [hi1, hi2, hi3]
          rw [h1, evalC_upd_ge E (Nat.le_refl c)] at hvC
          exact hvC
        obtain ⟨w, hwR, hwC⟩ := hpSub u hSub v hvR
        rw [evalC_Nc hM, evalC_Uc]
        intro hallW
        have hw1 := hallW w
        rw [evalC_Ic, evalC_Nc hM, evalC_Mc] at hw1
        have hw1C : evalC E c (upd (upd (upd (upd (upd (upd env c C) a z) b p) b u) a v) a w) := by
          have h2 : upd (upd (upd (upd (upd (upd env c C) a z) b p) b u) a v) a w =
              upd (upd (upd env b u) a w) c C := by
            funext i; unfold upd
            by_cases hi1 : i = c
            · subst hi1; simp [hca, hcb]
            · by_cases hi2 : i = a
              · subst hi2; simp [hi1]
              · by_cases hi3 : i = b
                · subst hi3; simp [hi1, hi2]
                · simp [hi1, hi2, hi3]
          rw [h2, evalC_upd_ge E (Nat.le_refl c)]
          exact hwR
        have hnwC := hw1 hw1C
        have hwa : upd (upd (upd (upd (upd (upd env c C) a z) b p) b u) a v) a w a = w := by simp [upd]
        have hwc : upd (upd (upd (upd (upd (upd env c C) a z) b p) b u) a v) a w c = C := by
          simp [upd, hca, hcb]
        rw [hwa, hwc] at hnwC
        exact hnwC hwC
      have hRhs := hG hLhs
      rw [evalC_Nc hM, evalC_Ic, evalC_Mc] at hRhs
      apply hRhs
      intro hcC
      rw [evalC_upd_ge E (Nat.le_refl c)] at hcC
      have hfa : upd env c C a = env a := by simp [upd, Ne.symm hca]
      have hfc : upd env c C c = C := by simp [upd]
      rw [hfa, hfc]
      exact hPt hcC
    -- Now split on a = b vs a ≠ b!
    by_cases hab : a = b
    · subst hab
      by_cases hc : evalC E c env
      · obtain ⟨C, hC⟩ := ax_pair hM (env a) (env a)
        apply hGateContra C
        · intro _; exact (hC (env a)).mpr (Or.inl rfl)
        · intro z hzC
          have hzeq : z = env a := by cases (hC z).mp hzC with | inl h => exact h | inr h => exact h
          subst hzeq
          refine ⟨env a, ?_, fun u _ v _ => ⟨env a, ?_, (hC (env a)).mpr (Or.inl rfl)⟩⟩
          · rw [upd_self, upd_id]; exact hc
          · rw [upd_self, upd_id]; exact hc
      · obtain ⟨C, hC⟩ := ax_empty hM
        exact hGateContra C (fun h => False.elim (hc h)) (fun z hzC => False.elim (hC z hzC))
    · -- a ≠ b: apply definable_pointed_hull!
      let relMap : Nat → Nat := fun i => if i = a then 0 else if i = b then 1 else i + 2
      let fR : Formula := rename relMap (codeToFormula c)
      have hRBd : Bound fR (c + 2) := by
        apply bound_rename (codeToFormula c) c (c + 2) relMap (bound_codeToFormula c)
        intro i hi; unfold relMap; split; omega; split <;> omega
      let ps := envParams env c
      have hlen : ps.length = c := envParams_length env c
      obtain ⟨C, hPt, hCl⟩ := definable_pointed_hull hM c fR hRBd ps hlen (env b) (env a)
      have hR_iff : ∀ u v,
          eval E fR (pushValue (pushValue (pushParams (fun _ => arbV) ps) u) v) ↔
          evalC E c (upd (upd env b u) a v) := by
        intro u v
        rw [eval_rename, eval_codeToFormula]
        apply evalC_congr
        intro i hi
        unfold relMap upd
        by_cases hia : i = a
        · subst hia; simp [pushValue]
        · by_cases hib : i = b
          · subst hib; simp [hia, pushValue]
          · simp only [hia, hib, ↓reduceIte, pushValue]
            exact pushParams_envParams_exact _ env c i hi
      apply hGateContra C
      · intro hc
        apply hPt
        rw [hR_iff, upd_id, upd_id]
        exact hc
      · intro z hzC
        obtain ⟨⟨p, hp⟩, hsub⟩ := hCl z hzC
        rw [hR_iff] at hp
        refine ⟨p, ?_, fun u hu v hv => ?_⟩
        · rwa [upd_comm env hab]
        · rw [if_neg hab] at hu
          obtain ⟨w, hwC, hRuw⟩ := hsub u hu ⟨v, (hR_iff u v).mpr hv⟩
          exact ⟨w, (hR_iff u w).mp hRuw, hwC⟩

theorem not_provC_one (hM : Model E) [Nonempty V] : ¬ ProvC 1 := by
  intro h1
  have h := provC_sound hM h1 (fun _ => arbV)
  rw [evalC_one] at h
  exact mem_irrefl hM _ h

end ZFModel

end DevCalcSound

theorem solution : (∃ (V : Type) (E : V → V → Prop), Nonempty V ∧ Model E) → ¬ PalomarZF207Calc.ProvC 1 := by
  rintro ⟨V, E, hNE, hM⟩
  exact @DevCalcSound.not_provC_one V E hM hNE
