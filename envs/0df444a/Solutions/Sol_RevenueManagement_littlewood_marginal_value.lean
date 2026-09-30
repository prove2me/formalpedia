-- Prove2me | solution 1 for RevenueManagement.littlewood_marginal_value
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T23:51:02.26579+00:00
-- url     : https://prove2.me/submissions/5ae8a520-c172-4053-b1a7-be3431e8a14f

import Mathlib
import Definitions.Def_RevenueManagement_singleResource

namespace RevenueManagement

open Finset

/-! ### Discrete concavity and the max-plus step -/

/-- Discrete concavity on `ℕ` from `1` on: `g(x+1) - g(x) ≤ g(x) - g(x-1)` for `x ≥ 1`. -/
def RMConc (g : ℕ → ℝ) : Prop := ∀ x, 1 ≤ x → g (x + 1) - g x ≤ g x - g (x - 1)

lemma rm_conc_mono {g : ℕ → ℝ} (hg : RMConc g) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    g b - g (b - 1) ≤ g a - g (a - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction n with
  | zero => simp
  | succ m ih =>
    have h1 := hg (a + m) (by omega)
    have e1 : a + (m + 1) = a + m + 1 := by ring
    have e2 : a + m + 1 - 1 = a + m := by omega
    rw [e1, e2]
    exact le_trans h1 (ih (by omega))

/-- `H(x) = max_{0 ≤ u ≤ min d x} (r u + g(x − u))`, the inner maximization of (2.3). -/
noncomputable def rmH (d : ℕ) (r : ℝ) (g : ℕ → ℝ) (x : ℕ) : ℝ :=
  (Finset.range (min d x + 1)).sup' ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩
    (fun u => r * u + g (x - u))

lemma rmH_ge (d : ℕ) (r : ℝ) (g : ℕ → ℝ) (x u : ℕ) (hu : u ≤ min d x) :
    r * u + g (x - u) ≤ rmH d r g x := by
  unfold rmH
  exact Finset.le_sup' (fun u : ℕ => r * (u : ℝ) + g (x - u)) (Finset.mem_range.2 (by omega))

lemma rmH_attained (d : ℕ) (r : ℝ) (g : ℕ → ℝ) (x : ℕ) :
    ∃ u, u ≤ min d x ∧ rmH d r g x = r * u + g (x - u) := by
  unfold rmH
  obtain ⟨u, hu, he⟩ := Finset.exists_mem_eq_sup' ⟨0, Finset.mem_range.2 (Nat.succ_pos (min d x))⟩
    (fun u : ℕ => r * (u : ℝ) + g (x - u))
  exact ⟨u, by simp only [Finset.mem_range] at hu; omega, he⟩

lemma rmH_zero (d : ℕ) (r : ℝ) (g : ℕ → ℝ) : rmH d r g 0 = g 0 := by
  apply le_antisymm
  · obtain ⟨u, hu, he⟩ := rmH_attained d r g 0
    have : u = 0 := by omega
    subst this; rw [he]; simp
  · have := rmH_ge d r g 0 0 (by omega); simpa using this

/-- Lemma (A): the marginal value of `H` dominates that of `g`. -/
lemma rmH_delta_ge {g : ℕ → ℝ} (hg : RMConc g) (d : ℕ) (r : ℝ) (x : ℕ) (hx : 1 ≤ x) :
    g x - g (x - 1) ≤ rmH d r g x - rmH d r g (x - 1) := by
  obtain ⟨u, hu, he⟩ := rmH_attained d r g (x - 1)
  have h1 := rmH_ge d r g x u (by omega)
  have h2 := rm_conc_mono hg (a := x - u) (b := x) (by omega) (by omega)
  have e : x - 1 - u = x - u - 1 := by omega
  rw [he, e]
  linarith

/-- Lemma 2-2.A.1: `H` is concave when `g` is. -/
lemma rmH_conc {g : ℕ → ℝ} (hg : RMConc g) (d : ℕ) (r : ℝ) : RMConc (rmH d r g) := by
  intro x hx
  obtain ⟨u1, hu1, he1⟩ := rmH_attained d r g (x + 1)
  obtain ⟨u2, hu2, he2⟩ := rmH_attained d r g (x - 1)
  rcases lt_or_ge u2 u1 with h | h
  · have ha := rmH_ge d r g x (u1 - 1) (by omega)
    have hb := rmH_ge d r g x (u2 + 1) (by omega)
    have e1 : x - (u1 - 1) = x + 1 - u1 := by omega
    have e2 : x - (u2 + 1) = x - 1 - u2 := by omega
    rw [e1] at ha; rw [e2] at hb
    have c1 : ((u1 - 1 : ℕ) : ℝ) = (u1 : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [c1] at ha; push_cast at hb
    rw [he1, he2]; linarith
  · have ha := rmH_ge d r g x u1 (by omega)
    have hb := rmH_ge d r g x u2 (by omega)
    have hc := rm_conc_mono hg (a := x - u2) (b := x + 1 - u1) (by omega) (by omega)
    have e1 : x + 1 - u1 - 1 = x - u1 := by omega
    have e2 : x - u2 - 1 = x - 1 - u2 := by omega
    rw [e1, e2] at hc
    rw [he1, he2]; linarith

lemma rmH_bound (d : ℕ) (r : ℝ) (g : ℕ → ℝ) (x : ℕ) :
    |rmH d r g x| ≤ |r| * x + ∑ k ∈ range (x + 1), |g k| := by
  have hS : ∀ k ≤ x, |g k| ≤ ∑ k ∈ range (x + 1), |g k| := fun k hk =>
    Finset.single_le_sum (f := fun k => |g k|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega))
  obtain ⟨u, hu, he⟩ := rmH_attained d r g x
  have h0 := rmH_ge d r g x 0 (by omega)
  simp only [Nat.cast_zero, mul_zero, zero_add, Nat.sub_zero] at h0
  have hgx := hS x le_rfl
  have hgu := hS (x - u) (by omega)
  have hru : r * u ≤ |r| * x := by
    have : (u : ℝ) ≤ x := by exact_mod_cast (show u ≤ x by omega)
    calc r * u ≤ |r| * u := mul_le_mul_of_nonneg_right (le_abs_self r) (Nat.cast_nonneg _)
      _ ≤ |r| * x := mul_le_mul_of_nonneg_left this (abs_nonneg r)
  have hr0 : 0 ≤ |r| * x := by positivity
  rw [abs_le]
  constructor
  · have := neg_abs_le (g x); linarith
  · have := le_abs_self (g (x - u)); rw [he]; linarith

lemma rm_summable (f : ℕ → ℝ) (hf : IsPmf f) (r : ℝ) (g : ℕ → ℝ) (x : ℕ) :
    Summable (fun d => f d * rmH d r g x) := by
  refine Summable.of_norm_bounded (hf.2.summable.mul_right (|r| * x + ∑ k ∈ range (x + 1), |g k|))
    (fun d => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf.1 d)]
  exact mul_le_mul_of_nonneg_left (rmH_bound d r g x) (hf.1 d)

/-- Expectation of the max-plus step against a pmf: concave, with dominating marginals. -/
lemma rm_expect {g : ℕ → ℝ} (hg : RMConc g) (f : ℕ → ℝ) (hf : IsPmf f) (r : ℝ) :
    RMConc (fun x => ∑' d, f d * rmH d r g x) ∧
      ∀ x, 1 ≤ x → g x - g (x - 1) ≤
        (∑' d, f d * rmH d r g x) - ∑' d, f d * rmH d r g (x - 1) := by
  have hs := rm_summable f hf r g
  have hsub : ∀ a b, (∑' d, f d * rmH d r g a) - ∑' d, f d * rmH d r g b
      = ∑' d, f d * (rmH d r g a - rmH d r g b) := by
    intro a b
    rw [← (hs a).tsum_sub (hs b)]
    congr 1; ext d; ring
  constructor
  · intro x hx
    simp only
    rw [hsub, hsub]
    have e : x + 1 - 1 = x := by omega
    refine Summable.tsum_le_tsum (fun d => ?_) ?_ ?_
    · have := rmH_conc hg d r x hx
      try rw [e] at this
      exact mul_le_mul_of_nonneg_left this (hf.1 d)
    · exact ((hs (x + 1)).sub (hs x)).congr (fun d => by ring)
    · exact ((hs x).sub (hs (x - 1))).congr (fun d => by ring)
  · intro x hx
    rw [hsub]
    have h1 : g x - g (x - 1) = ∑' d, f d * (g x - g (x - 1)) := by
      rw [tsum_mul_right, hf.2.tsum_eq, one_mul]
    rw [h1]
    refine Summable.tsum_le_tsum (fun d => ?_) (hf.2.summable.mul_right _) ?_
    · exact mul_le_mul_of_nonneg_left (rmH_delta_ge hg d r x hx) (hf.1 d)
    · exact ((hs x).sub (hs (x - 1))).congr (fun d => by ring)

/-! ### The static model -/

lemma static_succ (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (j x : ℕ) :
    staticValue p f (j + 1) x = ∑' d, f (j + 1) d * rmH d (p (j + 1)) (staticValue p f j) x := rfl

lemma static_conc (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (hf : ∀ j, IsPmf (f j)) :
    ∀ j, RMConc (staticValue p f j) := by
  intro j
  induction j with
  | zero => intro x _; simp [staticValue]
  | succ j ih =>
    have := (rm_expect ih (f (j + 1)) (hf (j + 1)) (p (j + 1))).1
    intro x hx
    simp only [static_succ]
    exact this x hx

lemma static_mono (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (hf : ∀ j, IsPmf (f j)) (j x : ℕ) (hx : 1 ≤ x) :
    staticDelta p f j x ≤ staticDelta p f (j + 1) x := by
  unfold staticDelta
  rw [static_succ, static_succ]
  exact (rm_expect (static_conc p f hf j) (f (j + 1)) (hf (j + 1)) (p (j + 1))).2 x hx

/-- Stage optimality from a threshold: the objective increases up to `u*` and decreases after. -/
lemma rm_stage_opt {g : ℕ → ℝ} (r : ℝ) (d x ustar : ℕ) (hu : ustar ≤ min d x)
    (hleft : ∀ v, v < ustar → g (x - v) - g (x - v - 1) ≤ r)
    (hright : ∀ v, ustar ≤ v → v < min d x → r ≤ g (x - v) - g (x - v - 1)) :
    ∀ u' ≤ min d x, r * u' + g (x - u') ≤ r * ustar + g (x - ustar) := by
  have step : ∀ v, v < x → r * ((v + 1 : ℕ) : ℝ) + g (x - (v + 1))
      = r * v + g (x - v) + (r - (g (x - v) - g (x - v - 1))) := by
    intro v hv
    have e : x - (v + 1) = x - v - 1 := by omega
    rw [e]; push_cast; ring
  intro u' hu'
  rcases le_or_gt u' ustar with h | h
  · obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le h
    clear h
    induction n generalizing u' with
    | zero => simp at hn; rw [hn]
    | succ m ih =>
      have h1 := ih (u' + 1) (by omega) (by omega)
      have h2 := step u' (by omega)
      have h3 := hleft u' (by omega)
      linarith
  · obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_lt h
    clear h
    induction n generalizing u' with
    | zero =>
      have h2 := step ustar (by omega)
      have h3 := hright ustar le_rfl (by omega)
      rw [hn]; linarith
    | succ m ih =>
      have h1 := ih (u' - 1) (by omega) (by omega)
      have h2 := step (u' - 1) (by omega)
      have h3 := hright (u' - 1) (by omega) (by omega)
      have e : u' - 1 + 1 = u' := by omega
      rw [e] at h2
      linarith

lemma rm_sup_mem {s : Finset ℕ} (h : 1 ≤ s.sup id) : s.sup id ∈ s := by
  have hne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; rintro rfl; simp at h
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup s hne id
  rw [he]; exact hi

/-! ### The dynamic model -/

lemma rmH_one (r : ℝ) (g : ℕ → ℝ) (x : ℕ) :
    rmH 1 r g (x + 1) = g (x + 1) + max (r - (g (x + 1) - g x)) 0 := by
  apply le_antisymm
  · obtain ⟨u, hu, he⟩ := rmH_attained 1 r g (x + 1)
    rw [he]
    have : u = 0 ∨ u = 1 := by omega
    rcases this with rfl | rfl
    · simp only [Nat.cast_zero, mul_zero, zero_add, Nat.sub_zero]
      have := le_max_right (r - (g (x + 1) - g x)) 0; linarith
    · have e : x + 1 - 1 = x := by omega
      simp only [Nat.cast_one, mul_one, e]
      have := le_max_left (r - (g (x + 1) - g x)) 0; linarith
  · have h0 := rmH_ge 1 r g (x + 1) 0 (by omega)
    have h1 := rmH_ge 1 r g (x + 1) 1 (by omega)
    have e : x + 1 - 1 = x := by omega
    simp only [Nat.cast_zero, mul_zero, zero_add, Nat.sub_zero] at h0
    simp only [Nat.cast_one, mul_one, e] at h1
    rcases le_total (r - (g (x + 1) - g x)) 0 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith

lemma dyn_zero (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T k : ℕ) : dynValueGo lam p n T k 0 = 0 := by
  cases k <;> simp [dynValueGo]

/-- The dynamic Bellman step as a mixture of max-plus steps. -/
lemma dyn_succ_eq (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T k y : ℕ) :
    dynValueGo lam p n T (k + 1) y
      = ∑ j ∈ Icc 1 n, lam j (T - k) * rmH 1 (p j) (dynValueGo lam p n T k) y
        + (1 - ∑ j ∈ Icc 1 n, lam j (T - k)) * rmH 1 0 (dynValueGo lam p n T k) y := by
  cases y with
  | zero =>
    simp only [rmH_zero, dyn_zero]; simp [dynValueGo]
  | succ x =>
    simp only [rmH_one]
    simp only [dynValueGo]
    rw [Finset.sum_congr rfl (fun j _ => mul_add (lam j (T - k)) _ _), Finset.sum_add_distrib,
      ← Finset.sum_mul]
    ring

lemma dyn_step (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T : ℕ) (hlam : IsArrivalModel lam n) (k : ℕ)
    (hk : RMConc (dynValueGo lam p n T k)) :
    RMConc (dynValueGo lam p n T (k + 1)) ∧
      ∀ x, 1 ≤ x → dynValueGo lam p n T k x - dynValueGo lam p n T k (x - 1)
        ≤ dynValueGo lam p n T (k + 1) x - dynValueGo lam p n T (k + 1) (x - 1) := by
  set g := dynValueGo lam p n T k with hgdef
  set w := fun j => lam j (T - k) with hw
  have hw0 : ∀ j, 0 ≤ w j := fun j => hlam.1 j _
  have hW : 0 ≤ 1 - ∑ j ∈ Icc 1 n, w j := by have := hlam.2 (T - k); simp only [hw]; linarith
  have hdiff : ∀ a b, dynValueGo lam p n T (k + 1) a - dynValueGo lam p n T (k + 1) b
      = ∑ j ∈ Icc 1 n, w j * (rmH 1 (p j) g a - rmH 1 (p j) g b)
        + (1 - ∑ j ∈ Icc 1 n, w j) * (rmH 1 0 g a - rmH 1 0 g b) := by
    intro a b
    rw [dyn_succ_eq, dyn_succ_eq]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  constructor
  · intro x hx
    rw [hdiff, hdiff]
    have e : x + 1 - 1 = x := by omega
    have h1 : ∑ j ∈ Icc 1 n, w j * (rmH 1 (p j) g (x + 1) - rmH 1 (p j) g x)
        ≤ ∑ j ∈ Icc 1 n, w j * (rmH 1 (p j) g x - rmH 1 (p j) g (x - 1)) := by
      apply Finset.sum_le_sum; intro j _
      have := rmH_conc hk 1 (p j) x hx; try rw [e] at this
      exact mul_le_mul_of_nonneg_left this (hw0 j)
    have h2 := rmH_conc hk 1 0 x hx; try rw [e] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 hW
    linarith
  · intro x hx
    rw [hdiff]
    have h1 : ∑ j ∈ Icc 1 n, w j * (g x - g (x - 1))
        ≤ ∑ j ∈ Icc 1 n, w j * (rmH 1 (p j) g x - rmH 1 (p j) g (x - 1)) := by
      apply Finset.sum_le_sum; intro j _
      exact mul_le_mul_of_nonneg_left (rmH_delta_ge hk 1 (p j) x hx) (hw0 j)
    have h2 := mul_le_mul_of_nonneg_left (rmH_delta_ge hk 1 0 x hx) hW
    rw [← Finset.sum_mul] at h1
    linarith

lemma dyn_conc (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T : ℕ) (hlam : IsArrivalModel lam n) :
    ∀ k, RMConc (dynValueGo lam p n T k) := by
  intro k
  induction k with
  | zero => intro x _; simp [dynValueGo]
  | succ k ih => exact (dyn_step lam p n T hlam k ih).1

/-! ### The choice model -/

/-- `Φ(δ) = max_S λ (R(S) − Q(S) δ)`. -/
noncomputable def choicePhi {n : ℕ} (l : ℝ) (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ)
    (δ : ℝ) : ℝ :=
  (Finset.univ : Finset (Finset (Fin n))).sup' Finset.univ_nonempty
    (fun S => l * (expRevenue P p S - purchaseProb P S * δ))

section Phi

variable {n : ℕ} (l : ℝ) (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ)

lemma purchaseProb_nonneg (hP : IsChoiceModel P) (S : Finset (Fin n)) : 0 ≤ purchaseProb P S :=
  Finset.sum_nonneg (fun j _ => hP.1 S j)

lemma phi_ge (δ : ℝ) (S : Finset (Fin n)) :
    l * (expRevenue P p S - purchaseProb P S * δ) ≤ choicePhi l P p δ := by
  unfold choicePhi
  exact Finset.le_sup' (fun S => l * (expRevenue P p S - purchaseProb P S * δ)) (Finset.mem_univ S)

lemma phi_nonneg (δ : ℝ) : 0 ≤ choicePhi l P p δ := by
  have := phi_ge l P p δ ∅
  simp [expRevenue, purchaseProb] at this
  exact this

lemma phi_anti (hl : 0 ≤ l) (hP : IsChoiceModel P) {δ1 δ2 : ℝ} (h : δ1 ≤ δ2) :
    choicePhi l P p δ2 ≤ choicePhi l P p δ1 := by
  unfold choicePhi
  apply Finset.sup'_le
  intro S _
  refine le_trans ?_ (phi_ge l P p δ1 S)
  have := purchaseProb_nonneg P hP S
  apply mul_le_mul_of_nonneg_left _ hl
  nlinarith

lemma phi_lip (hl : 0 ≤ l) (hl1 : l ≤ 1) (hP : IsChoiceModel P) {δ1 δ2 : ℝ} (h : δ1 ≤ δ2) :
    choicePhi l P p δ1 ≤ choicePhi l P p δ2 + (δ2 - δ1) := by
  obtain ⟨S, _, he⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Finset (Fin n))))
    Finset.univ_nonempty (fun S => l * (expRevenue P p S - purchaseProb P S * δ1))
  have h1 := phi_ge l P p δ2 S
  unfold choicePhi at *
  rw [he]
  have hq0 := purchaseProb_nonneg P hP S
  have hq1 : purchaseProb P S ≤ 1 := hP.2 S
  have hlq : l * purchaseProb P S ≤ 1 := by nlinarith
  have hd : 0 ≤ δ2 - δ1 := by linarith
  nlinarith

end Phi

lemma choice_zero {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ)
    (T k : ℕ) : choiceValueGo lam P p T k 0 = 0 := by
  cases k <;> simp [choiceValueGo]

lemma choice_succ {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ)
    (T k y : ℕ) :
    choiceValueGo lam P p T (k + 1) (y + 1)
      = choicePhi (lam (T - k)) P p
          (choiceValueGo lam P p T k (y + 1) - choiceValueGo lam P p T k y)
        + choiceValueGo lam P p T k (y + 1) := by
  simp only [choiceValueGo, choicePhi]

/-- The abstract step of Proposition 2-2.A.4. -/
lemma choice_step_abstract (V V' : ℕ → ℝ) (Φ : ℝ → ℝ) (hΦ0 : ∀ δ, 0 ≤ Φ δ)
    (hanti : ∀ δ1 δ2, δ1 ≤ δ2 → Φ δ2 ≤ Φ δ1)
    (hlip : ∀ δ1 δ2, δ1 ≤ δ2 → Φ δ1 ≤ Φ δ2 + (δ2 - δ1))
    (hV0 : V 0 = 0) (hV'0 : V' 0 = 0) (hV' : ∀ y, V' (y + 1) = Φ (V (y + 1) - V y) + V (y + 1))
    (hV : RMConc V) :
    RMConc V' ∧ ∀ x, 1 ≤ x → V x - V (x - 1) ≤ V' x - V' (x - 1) := by
  constructor
  · intro x hx
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hc := hV (y + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hc
    have h1 := hlip _ _ hc
    cases y with
    | zero =>
      rw [hV' (0 + 1), hV' 0, hV'0]
      have := hΦ0 (V (0 + 1) - V 0)
      simp only [hV0] at hc h1 this ⊢
      linarith
    | succ z =>
      rw [hV' (z + 1 + 1), hV' (z + 1), hV' z]
      have hc2 := hV (z + 1) (by omega)
      simp only [Nat.add_sub_cancel] at hc2
      have h2 := hanti _ _ hc2
      linarith
  · intro x hx
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    cases y with
    | zero =>
      rw [hV' 0, hV'0]
      have := hΦ0 (V (0 + 1) - V 0)
      simp only [hV0] at this ⊢
      linarith
    | succ z =>
      rw [hV' (z + 1), hV' z]
      have hc2 := hV (z + 1) (by omega)
      simp only [Nat.add_sub_cancel] at hc2
      have h2 := hanti _ _ hc2
      linarith

section ChoiceProps

variable {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ) (T : ℕ)
  (hP : IsChoiceModel P) (hlam : ∀ t, 0 ≤ lam t ∧ lam t ≤ 1)
include hP hlam

lemma choice_step (k : ℕ) (hk : RMConc (choiceValueGo lam P p T k)) :
    RMConc (choiceValueGo lam P p T (k + 1)) ∧
      ∀ x, 1 ≤ x → choiceValueGo lam P p T k x - choiceValueGo lam P p T k (x - 1)
        ≤ choiceValueGo lam P p T (k + 1) x - choiceValueGo lam P p T (k + 1) (x - 1) :=
  choice_step_abstract _ _ (choicePhi (lam (T - k)) P p) (phi_nonneg _ P p)
    (fun _ _ h => phi_anti _ P p (hlam _).1 hP h)
    (fun _ _ h => phi_lip _ P p (hlam _).1 (hlam _).2 hP h)
    (choice_zero lam P p T k) (choice_zero lam P p T (k + 1)) (choice_succ lam P p T k) hk

lemma choice_conc (k : ℕ) : RMConc (choiceValueGo lam P p T k) := by
  induction k with
  | zero => intro x _; simp [choiceValueGo]
  | succ k ih => exact (choice_step lam P p T hP hlam k ih).1

lemma choiceDelta_conc (s x x' : ℕ) (hx : 1 ≤ x) (hxx : x ≤ x') :
    choiceDelta lam P p T s x' ≤ choiceDelta lam P p T s x := by
  unfold choiceDelta choiceValue
  exact rm_conc_mono (choice_conc lam P p T hP hlam _) hx hxx

lemma choiceDelta_time (s x : ℕ) (hx : 1 ≤ x) :
    choiceDelta lam P p T (s + 1) x ≤ choiceDelta lam P p T s x := by
  unfold choiceDelta choiceValue
  rcases le_or_gt s T with hs | hs
  · have e1 : T + 1 - s = (T + 1 - (s + 1)) + 1 := by omega
    rw [e1]
    exact (choice_step lam P p T hP hlam _ (choice_conc lam P p T hP hlam _)).2 x hx
  · have e1 : T + 1 - s = 0 := by omega
    have e2 : T + 1 - (s + 1) = 0 := by omega
    rw [e1, e2]

lemma choiceDelta_time' (s s' x : ℕ) (hx : 1 ≤ x) (hss : s ≤ s') :
    choiceDelta lam P p T s' x ≤ choiceDelta lam P p T s x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hss
  clear hss
  induction m with
  | zero => simp
  | succ m ih =>
    exact le_trans (choiceDelta_time lam P p T hP hlam (s + m) x hx) ih

lemma choiceDelta_nonneg (s x : ℕ) (hx : 1 ≤ x) : 0 ≤ choiceDelta lam P p T s x := by
  unfold choiceDelta choiceValue
  generalize T + 1 - s = k
  induction k with
  | zero => simp [choiceValueGo]
  | succ k ih =>
    exact le_trans ih ((choice_step lam P p T hP hlam k (choice_conc lam P p T hP hlam k)).2 x hx)

/-- Proposition 2.3. -/
lemma choice_ineff_not_opt (t x : ℕ) (hx : 1 ≤ x) (hpos : 0 < lam t)
    (S : Finset (Fin n)) (hS : IsInefficient P p S) : ¬ IsChoiceOptimal lam P p T t x S := by
  intro hopt
  obtain ⟨α, hα0, hα1, hαQ, hαR⟩ := hS
  set Δ := choiceDelta lam P p T (t + 1) x with hΔ
  have hΔ0 : 0 ≤ Δ := choiceDelta_nonneg lam P p T hP hlam (t + 1) x hx
  have h1 : ∑ S', α S' * choiceObj lam P p T t x S' ≤ ∑ S', α S' * choiceObj lam P p T t x S :=
    Finset.sum_le_sum (fun S' _ => mul_le_mul_of_nonneg_left (hopt S') (hα0 S'))
  rw [← Finset.sum_mul, hα1, one_mul] at h1
  have h2 : ∑ S', α S' * choiceObj lam P p T t x S'
      = lam t * (∑ S', α S' * expRevenue P p S') - lam t * Δ * (∑ S', α S' * purchaseProb P S') := by
    unfold choiceObj
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro S' _; ring
  rw [h2] at h1
  unfold choiceObj at h1
  rw [← hΔ] at h1
  have h3 : lam t * Δ * (∑ S', α S' * purchaseProb P S') ≤ lam t * Δ * purchaseProb P S :=
    mul_le_mul_of_nonneg_left hαQ (mul_nonneg (le_of_lt hpos) hΔ0)
  have h4 : lam t * expRevenue P p S < lam t * (∑ S', α S' * expRevenue P p S') :=
    mul_lt_mul_of_pos_left hαR hpos
  nlinarith

end ChoiceProps

/-- Ordering of efficient sets. -/
lemma efficient_ordered {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ)
    (S S' : Finset (Fin n)) (hS' : IsEfficient P p S')
    (hQ : purchaseProb P S ≤ purchaseProb P S') : expRevenue P p S ≤ expRevenue P p S' := by
  by_contra hlt
  push Not at hlt
  apply hS'
  refine ⟨fun S'' => if S'' = S then 1 else 0, fun S'' => by dsimp only; split_ifs <;> norm_num, ?_, ?_, ?_⟩
  · simp
  · simp only [ite_mul, one_mul, zero_mul]; simpa using hQ
  · simp only [ite_mul, one_mul, zero_mul]; simpa using hlt

/-- The Bellman equation (2.26) in terms of the objective. -/
lemma choice_bellman {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ)
    (T t y : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) :
    choiceValue lam P p T t (y + 1)
      = (Finset.univ : Finset (Finset (Fin n))).sup' Finset.univ_nonempty
          (fun S => choiceObj lam P p T t (y + 1) S) + choiceValue lam P p T (t + 1) (y + 1) := by
  unfold choiceObj choiceDelta choiceValue
  rw [show T + 1 - t = (T - t) + 1 by omega, show T + 1 - (t + 1) = T - t by omega, choice_succ]
  unfold choicePhi
  rw [show T - (T - t) = t by omega]
  simp only [Nat.add_sub_cancel]

/-- Monotone comparative statics of `R(S) − Q(S) Δ` in `Δ`. -/
lemma choice_argmax_mono {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ)
    (Δ' Δ : ℝ) (hΔ : Δ' ≤ Δ) (S : Finset (Fin n))
    (hS : ∀ S'', expRevenue P p S'' - purchaseProb P S'' * Δ ≤
      expRevenue P p S - purchaseProb P S * Δ) :
    ∃ S', (∀ S'', expRevenue P p S'' - purchaseProb P S'' * Δ' ≤
      expRevenue P p S' - purchaseProb P S' * Δ') ∧ purchaseProb P S ≤ purchaseProb P S' := by
  classical
  set M := (Finset.univ : Finset (Finset (Fin n))).filter (fun S' => ∀ S'',
    expRevenue P p S'' - purchaseProb P S'' * Δ' ≤ expRevenue P p S' - purchaseProb P S' * Δ')
    with hM
  obtain ⟨S0, _, h0⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Finset (Fin n))))
    Finset.univ_nonempty (fun S => expRevenue P p S - purchaseProb P S * Δ')
  have hne : M.Nonempty := ⟨S0, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun S'' => by
    rw [← h0]
    exact Finset.le_sup' (fun S => expRevenue P p S - purchaseProb P S * Δ') (Finset.mem_univ S'')⟩⟩
  obtain ⟨S', hS'M, hmax⟩ := Finset.exists_max_image M (purchaseProb P) hne
  have hS'opt := (Finset.mem_filter.1 hS'M).2
  refine ⟨S', hS'opt, ?_⟩
  by_contra hlt
  push Not at hlt
  have h1 := hS S'
  have h2 := hS'opt S
  have hge : Δ ≤ Δ' := by
    by_contra hc
    push Not at hc
    nlinarith [mul_pos (sub_pos.2 hlt) (sub_pos.2 hc)]
  have hΔeq : Δ' = Δ := le_antisymm hΔ hge
  subst hΔeq
  have hSM : S ∈ M := Finset.mem_filter.2 ⟨Finset.mem_univ _, hS⟩
  have := hmax S hSM
  linarith

end RevenueManagement

open RevenueManagement

theorem solution (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (hf : ∀ j, IsPmf (f j))
    (hp : ∀ j, 0 ≤ p j) (x : ℕ) (hx : 1 ≤ x) :
    staticDelta p f 1 x = p 1 * ∑' d, (if x ≤ d then f 1 d else 0) ∧
      (IsStageOptimal p f 1 x 1 1 ↔ p 1 * ∑' d, (if x ≤ d then f 1 d else 0) ≤ p 2) := by
  have hH : ∀ d y, rmH d (p 1) (staticValue p f 0) y = p 1 * ((min d y : ℕ) : ℝ) := by
    intro d y
    apply le_antisymm
    · obtain ⟨u, hu, he⟩ := rmH_attained d (p 1) (staticValue p f 0) y
      rw [he]; simp only [staticValue, add_zero]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hu) (hp 1)
    · have := rmH_ge d (p 1) (staticValue p f 0) y (min d y) le_rfl
      simp only [staticValue, add_zero] at this; exact this
  have hV1 : ∀ y, staticValue p f 1 y = ∑' d, f 1 d * (p 1 * ((min d y : ℕ) : ℝ)) := by
    intro y
    rw [static_succ]
    simp only [hH]
  have hs : ∀ y, Summable (fun d => f 1 d * (p 1 * ((min d y : ℕ) : ℝ))) := fun y =>
    (rm_summable (f 1) (hf 1) (p 1) (staticValue p f 0) y).congr (fun d => by rw [hH])
  have hΔ : staticDelta p f 1 x = p 1 * ∑' d, (if x ≤ d then f 1 d else 0) := by
    unfold staticDelta
    rw [hV1, hV1, ← (hs x).tsum_sub (hs (x - 1)), ← tsum_mul_left]
    congr 1; ext d
    by_cases h : x ≤ d
    · rw [if_pos h, min_eq_right h, min_eq_right (by omega : x - 1 ≤ d), Nat.cast_sub hx]
      push_cast; ring
    · rw [if_neg h, min_eq_left (by omega : d ≤ x), min_eq_left (by omega : d ≤ x - 1)]
      ring
  refine ⟨hΔ, ?_⟩
  rw [← hΔ]
  unfold IsStageOptimal staticDelta
  have e2 : (1 : ℕ) + 1 = 2 := rfl
  rw [e2]
  constructor
  · rintro ⟨_, h⟩
    have := h 0 (by omega)
    simp only [Nat.cast_zero, mul_zero, zero_add, Nat.sub_zero, Nat.cast_one, mul_one] at this
    linarith
  · intro h
    refine ⟨by omega, fun u' hu' => ?_⟩
    have : u' = 0 ∨ u' = 1 := by omega
    rcases this with rfl | rfl
    · simp only [Nat.cast_zero, mul_zero, zero_add, Nat.sub_zero, Nat.cast_one, mul_one]
      linarith
    · exact le_rfl
