-- Prove2me | solution 1 for RevenueManagement.overbooking_limit_policy
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T09:19:47.878989+00:00
-- url     : https://prove2.me/submissions/b9ad7f9b-ee7f-4da5-b951-653ee1702476

import Mathlib
import Definitions.Def_RevenueManagement_overbooking

namespace RevenueManagement

open Finset

/-! ### Discrete concavity on `ℕ` -/

/-- Nonincreasing increments. -/
def rm2Conc (W : ℕ → ℝ) : Prop := ∀ z, W (z + 1 + 1) - W (z + 1) ≤ W (z + 1) - W z

lemma rm2Conc.incr_anti {W : ℕ → ℝ} (hW : rm2Conc W) {a b : ℕ} (hab : a ≤ b) :
    W (b + 1) - W b ≤ W (a + 1) - W a := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction n with
  | zero => simp
  | succ m ih =>
    have h := hW (a + m)
    have ih' := ih (by omega)
    have e : a + (m + 1) = a + m + 1 := by ring
    rw [e]; linarith

/-- Moving two points towards each other does not decrease the sum. -/
lemma rm2Conc.pair {W : ℕ → ℝ} (hW : rm2Conc W) {c e : ℕ} (hce : c + 2 ≤ e) :
    W c + W e ≤ W (c + 1) + W (e - 1) := by
  have h := hW.incr_anti (a := c) (b := e - 1) (by omega)
  have e1 : e - 1 + 1 = e := by omega
  rw [e1] at h
  linarith

/-- After the first decrease, a concave sequence stays below. -/
lemma rm2Conc.decr_after {G : ℕ → ℝ} (hG : rm2Conc G) {z : ℕ} (hz : G (z + 1) < G z) :
    ∀ s, z < s → G s < G z := by
  intro s hs
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hs
  induction n with
  | zero => simpa using hz
  | succ m ih =>
    have h1 := hG.incr_anti (a := z) (b := z + m + 1) (by omega)
    have e : z + (m + 1) + 1 = z + m + 1 + 1 := by ring
    rw [e]
    have := ih (by omega)
    linarith

/-- Before a nonnegative increment, a concave sequence is nondecreasing. -/
lemma rm2Conc.incr_before {G : ℕ → ℝ} (hG : rm2Conc G) {z : ℕ} (hz : G z ≤ G (z + 1)) :
    ∀ x', x' ≤ z + 1 → G x' ≤ G (z + 1) := by
  have key : ∀ m x', x' + m = z + 1 → G x' ≤ G (z + 1) := by
    intro m
    induction m with
    | zero => intro x' h; rw [← h]; simp
    | succ m ih =>
      intro x' h
      have h1 := hG.incr_anti (a := x') (b := z) (by omega)
      have h2 := ih (x' + 1) (by omega)
      linarith
  intro x' hx'
  exact key (z + 1 - x') x' (by omega)

lemma rm2_mono_up (G : ℕ → ℝ) (a b : ℕ) (h : ∀ z, a ≤ z → z < b → G z ≤ G (z + 1)) :
    ∀ u v, a ≤ u → u ≤ v → v ≤ b → G u ≤ G v := by
  intro u v hu huv hvb
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le huv
  induction n with
  | zero => simp
  | succ m ih =>
    have := ih (by omega) (by omega)
    have := h (u + m) (by omega) (by omega)
    have e : u + (m + 1) = u + m + 1 := by ring
    rw [e]; linarith

lemma rm2_mono_down (G : ℕ → ℝ) (a : ℕ) (h : ∀ z, a ≤ z → G (z + 1) < G z) :
    ∀ u v, a ≤ u → u ≤ v → G v ≤ G u := by
  intro u v hu huv
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le huv
  induction n with
  | zero => simp
  | succ m ih =>
    have := ih (by omega)
    have := h (u + m) (by omega)
    have e : u + (m + 1) = u + m + 1 := by ring
    rw [e]; linarith

/-! ### The greatest optimal limit in `ℕ∞` -/

section ENatLimit

variable (G : ℕ → ℝ) (hG : rm2Conc G)
include hG

lemma rm2_enat_a (z : ℕ)
    (hz : (z : ℕ∞) < sSup ((fun x : ℕ => (x : ℕ∞)) '' {x | ∀ x' ≤ x, G x' ≤ G x})) :
    G z ≤ G (z + 1) := by
  rw [lt_sSup_iff] at hz
  obtain ⟨_, ⟨s, hs, rfl⟩, hzs⟩ := hz
  have hzs' : z < s := by
    have : (z : ℕ∞) < (s : ℕ∞) := hzs
    exact_mod_cast this
  by_contra h
  push Not at h
  have h1 := hG.decr_after h s hzs'
  have h2 := hs z (le_of_lt hzs')
  linarith

lemma rm2_enat_b (z : ℕ)
    (hz : sSup ((fun x : ℕ => (x : ℕ∞)) '' {x | ∀ x' ≤ x, G x' ≤ G x}) ≤ (z : ℕ∞)) :
    G (z + 1) < G z := by
  by_contra h
  push Not at h
  have hmem : z + 1 ∈ {x | ∀ x' ≤ x, G x' ≤ G x} := fun x' hx' => hG.incr_before h x' hx'
  have h1 := le_sSup (Set.mem_image_of_mem (fun x : ℕ => (x : ℕ∞)) hmem)
  have h2 := le_trans h1 hz
  have : z + 1 ≤ z := by exact_mod_cast h2
  omega

end ENatLimit

/-! ### Binomial thinning -/

/-- `E_q[W](x) = ∑_{z ≤ x} P(Bin(x, q) = z) W(z)`. -/
noncomputable def rm2E (q : ℝ) (W : ℕ → ℝ) (x : ℕ) : ℝ :=
  ∑ z ∈ range (x + 1), binomPmf q x z * W z

lemma rm2E_zero (q : ℝ) (W : ℕ → ℝ) : rm2E q W 0 = W 0 := by
  simp [rm2E, binomPmf]

/-- Pascal's rule: `Bin(x+1, q)` is `Bin(x, q)` plus an independent Bernoulli step. -/
lemma rm2E_succ (q : ℝ) (W : ℕ → ℝ) (x : ℕ) :
    rm2E q W (x + 1) = q * rm2E q (fun z => W (z + 1)) x + (1 - q) * rm2E q W x := by
  unfold rm2E binomPmf
  rw [Finset.sum_range_succ' _ (x + 1)]
  have e1 : ∀ k ∈ range (x + 1), ((x + 1).choose (k + 1) : ℝ) * q ^ (k + 1)
        * (1 - q) ^ (x + 1 - (k + 1)) * W (k + 1)
      = q * ((x.choose k : ℝ) * q ^ k * (1 - q) ^ (x - k) * W (k + 1))
        + (x.choose (k + 1) : ℝ) * q ^ (k + 1) * (1 - q) ^ (x - k) * W (k + 1) := by
    intro k _
    rw [Nat.choose_succ_succ, Nat.add_sub_add_right]
    push_cast; ring
  rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_range_succ (fun k => (x.choose (k + 1) : ℝ) * q ^ (k + 1) * (1 - q) ^ (x - k)
      * W (k + 1)) x]
  simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
  rw [Finset.sum_range_succ' (fun z => (x.choose z : ℝ) * q ^ z * (1 - q) ^ (x - z) * W z) x]
  have e2 : ∀ k ∈ range x, (x.choose (k + 1) : ℝ) * q ^ (k + 1) * (1 - q) ^ (x - k) * W (k + 1)
      = (1 - q) * ((x.choose (k + 1) : ℝ) * q ^ (k + 1) * (1 - q) ^ (x - (k + 1)) * W (k + 1)) := by
    intro k hk
    have : x - k = (x - (k + 1)) + 1 := by simp at hk; omega
    rw [this, pow_succ]; ring
  rw [Finset.sum_congr rfl e2, ← Finset.mul_sum]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, Nat.sub_zero, one_mul]
  ring

lemma rm2E_add (q : ℝ) (U W : ℕ → ℝ) (x : ℕ) :
    rm2E q (fun z => U z + W z) x = rm2E q U x + rm2E q W x := by
  simp only [rm2E, mul_add, Finset.sum_add_distrib]

lemma rm2E_sub (q : ℝ) (U W : ℕ → ℝ) (x : ℕ) :
    rm2E q (fun z => U z - W z) x = rm2E q U x - rm2E q W x := by
  simp only [rm2E, mul_sub, Finset.sum_sub_distrib]

lemma rm2E_smul (q a : ℝ) (W : ℕ → ℝ) (x : ℕ) :
    rm2E q (fun z => a * W z) x = a * rm2E q W x := by
  simp only [rm2E, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro z _; ring

lemma rm2E_one (q : ℝ) (x : ℕ) : rm2E q (fun _ => 1) x = 1 := by
  induction x with
  | zero => simp [rm2E_zero]
  | succ n ih => rw [rm2E_succ, ih]; ring

lemma rm2E_const (q c : ℝ) (x : ℕ) : rm2E q (fun _ => c) x = c := by
  have := rm2E_smul q c (fun _ => 1) x
  simp only [mul_one] at this
  rw [this, rm2E_one, mul_one]

lemma rm2E_id (q : ℝ) (x : ℕ) : rm2E q (fun z => (z : ℝ)) x = q * x := by
  induction x with
  | zero => simp [rm2E_zero]
  | succ n ih =>
    rw [rm2E_succ]
    have : rm2E q (fun z => ((z + 1 : ℕ) : ℝ)) n = rm2E q (fun z => (z : ℝ)) n + 1 := by
      have := rm2E_add q (fun z => (z : ℝ)) (fun _ => 1) n
      rw [rm2E_one] at this
      rw [← this]; push_cast; rfl
    rw [this, ih]; push_cast; ring

lemma rm2E_diff (q : ℝ) (W : ℕ → ℝ) (x : ℕ) :
    rm2E q W (x + 1) - rm2E q W x = q * rm2E q (fun z => W (z + 1) - W z) x := by
  rw [rm2E_succ, rm2E_sub]; ring

lemma binomPmf_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (x z : ℕ) : 0 ≤ binomPmf q x z := by
  unfold binomPmf
  have : 0 ≤ 1 - q := by linarith
  positivity

lemma rm2E_mono {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {U W : ℕ → ℝ} {x : ℕ}
    (h : ∀ z ≤ x, U z ≤ W z) : rm2E q U x ≤ rm2E q W x := by
  unfold rm2E
  apply Finset.sum_le_sum
  intro z hz
  have := h z (by simp at hz; omega)
  exact mul_le_mul_of_nonneg_left this (binomPmf_nonneg hq0 hq1 x z)

/-- Binomial thinning preserves discrete concavity. -/
lemma rm2E_conc {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {W : ℕ → ℝ} (hW : rm2Conc W) :
    rm2Conc (rm2E q W) := by
  intro x
  rw [rm2E_diff, rm2E_diff]
  have h1 := rm2E_diff q (fun z => W (z + 1) - W z) x
  have h2 : rm2E q (fun z => (W (z + 1 + 1) - W (z + 1)) - (W (z + 1) - W z)) x ≤ 0 := by
    have := rm2E_mono hq0 hq1 (U := fun z => (W (z + 1 + 1) - W (z + 1)) - (W (z + 1) - W z))
      (W := fun _ => 0) (x := x) (fun z _ => by have := hW z; linarith)
    rwa [rm2E_const] at this
  have h3 : rm2E q (fun z => W (z + 1) - W z) (x + 1) - rm2E q (fun z => W (z + 1) - W z) x ≤ 0 := by
    rw [h1]; exact mul_nonpos_of_nonneg_of_nonpos hq0 h2
  nlinarith

/-- The post-cancellation value `∑_z P(Bin(x,q) = z) (V z − (x − z) r) = E[V] − r (1 − q) x`. -/
lemma rm2_post_eq (q r : ℝ) (V : ℕ → ℝ) (x : ℕ) :
    ∑ z ∈ range (x + 1), binomPmf q x z * (V z - ((x : ℝ) - z) * r)
      = rm2E q V x - r * (1 - q) * x := by
  have e : ∀ z, binomPmf q x z * (V z - ((x : ℝ) - z) * r)
      = binomPmf q x z * V z - r * x * (binomPmf q x z * 1) + r * (binomPmf q x z * z) := by
    intro z; ring
  rw [Finset.sum_congr rfl (fun z _ => e z), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : ∑ i ∈ range (x + 1), binomPmf q x i * 1 = rm2E q (fun _ => 1) x := rfl
  have h2 : ∑ i ∈ range (x + 1), binomPmf q x i * (i : ℝ) = rm2E q (fun z => (z : ℝ)) x := rfl
  rw [h1, h2, rm2E_one, rm2E_id]
  unfold rm2E
  ring

lemma rm2_post_conc {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (r : ℝ) {V : ℕ → ℝ} (hV : rm2Conc V) :
    rm2Conc (fun x => ∑ z ∈ range (x + 1), binomPmf q x z * (V z - ((x : ℝ) - z) * r)) := by
  intro x
  simp only [rm2_post_eq]
  have := rm2E_conc hq0 hq1 hV x
  push_cast
  linarith

/-! ### The windowed maximum -/

/-- `W_d(y) = max_{y ≤ x ≤ y + d} (A x + (x − y) p)`. -/
noncomputable def rm2Win (A : ℕ → ℝ) (p : ℝ) (d y : ℕ) : ℝ :=
  (Icc y (y + d)).sup' ⟨y, mem_Icc.2 ⟨le_rfl, Nat.le_add_right _ _⟩⟩
    (fun x => A x + ((x : ℝ) - y) * p)

lemma rm2Win_ge (A : ℕ → ℝ) (p : ℝ) (d y x : ℕ) (h1 : y ≤ x) (h2 : x ≤ y + d) :
    A x + ((x : ℝ) - y) * p ≤ rm2Win A p d y := by
  unfold rm2Win
  exact Finset.le_sup' (fun x : ℕ => A x + ((x : ℝ) - y) * p) (mem_Icc.2 ⟨h1, h2⟩)

lemma rm2Win_attained (A : ℕ → ℝ) (p : ℝ) (d y : ℕ) :
    ∃ x, y ≤ x ∧ x ≤ y + d ∧ rm2Win A p d y = A x + ((x : ℝ) - y) * p := by
  unfold rm2Win
  obtain ⟨x, hx, he⟩ := Finset.exists_mem_eq_sup' (s := Icc y (y + d))
    ⟨y, mem_Icc.2 ⟨le_rfl, Nat.le_add_right _ _⟩⟩ (fun x : ℕ => A x + ((x : ℝ) - y) * p)
  exact ⟨x, (mem_Icc.1 hx).1, (mem_Icc.1 hx).2, he⟩

/-- The windowed maximum of a concave objective is concave in the window's position. -/
lemma rm2Win_conc {A : ℕ → ℝ} (hA : rm2Conc A) (p : ℝ) (d : ℕ) : rm2Conc (rm2Win A p d) := by
  intro y
  obtain ⟨a, ha1, ha2, hae⟩ := rm2Win_attained A p d (y + 1 + 1)
  obtain ⟨b, hb1, hb2, hbe⟩ := rm2Win_attained A p d y
  rw [hae, hbe]
  rcases le_or_gt (b + 2) a with hab | hab
  · have h1 := rm2Win_ge A p d (y + 1) (a - 1) (by omega) (by omega)
    have h2 := rm2Win_ge A p d (y + 1) (b + 1) (by omega) (by omega)
    have h3 := hA.pair hab
    have c1 : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [c1] at h1
    push_cast at h1 h2 ⊢
    nlinarith
  · have h1 := rm2Win_ge A p d (y + 1) a (by omega) (by omega)
    have h2 := rm2Win_ge A p d (y + 1) b (by omega) (by omega)
    push_cast at h1 h2 ⊢
    nlinarith

/-- One step of the window moves its maximum by a bounded amount, uniformly in `d`. -/
lemma rm2Win_step {A : ℕ → ℝ} (hA : rm2Conc A) (p : ℝ) (d y : ℕ) :
    |rm2Win A p d (y + 1) - rm2Win A p d y| ≤ |p| + |A 1 - A 0| + |A (y + 1) - A y| := by
  rw [abs_le]
  have hp1 := le_abs_self p
  have hp2 := neg_abs_le p
  have hA1 := le_abs_self (A 1 - A 0)
  have hA2 := neg_abs_le (A (y + 1) - A y)
  have hA3 := abs_nonneg (A 1 - A 0)
  have hA4 := abs_nonneg (A (y + 1) - A y)
  have hA5 := abs_nonneg p
  constructor
  · obtain ⟨x0, h1, h2, he⟩ := rm2Win_attained A p d y
    rw [he]
    rcases eq_or_lt_of_le h1 with h | h
    · subst h
      have := rm2Win_ge A p d (y + 1) (y + 1) le_rfl (by omega)
      push_cast at this ⊢
      linarith
    · have := rm2Win_ge A p d (y + 1) x0 (by omega) (by omega)
      push_cast at this ⊢
      linarith
  · obtain ⟨x1, h1, h2, he⟩ := rm2Win_attained A p d (y + 1)
    rw [he]
    rcases eq_or_lt_of_le h2 with h | h
    · subst h
      have h3 := rm2Win_ge A p d y (y + d) (by omega) le_rfl
      have h4 := hA.incr_anti (a := 0) (b := y + d) (Nat.zero_le _)
      have e : y + 1 + d = y + d + 1 := by ring
      rw [e]
      push_cast at h3 h4 ⊢
      linarith
    · have := rm2Win_ge A p d y x1 (by omega) (by omega)
      push_cast at this ⊢
      linarith

lemma rm2Win_bound {A : ℕ → ℝ} (hA : rm2Conc A) (p : ℝ) (d y : ℕ) :
    |rm2Win A p d y - rm2Win A p d 0|
      ≤ ∑ w ∈ range y, (|p| + |A 1 - A 0| + |A (w + 1) - A w|) := by
  induction y with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have := rm2Win_step hA p d n
    calc |rm2Win A p d (n + 1) - rm2Win A p d 0|
        = |(rm2Win A p d (n + 1) - rm2Win A p d n) + (rm2Win A p d n - rm2Win A p d 0)| := by
          ring_nf
      _ ≤ |rm2Win A p d (n + 1) - rm2Win A p d n| + |rm2Win A p d n - rm2Win A p d 0| :=
          abs_add_le _ _
      _ ≤ _ := by linarith

/-- Either the expected windowed maximum is summable at every position or at none. -/
lemma rm2_summable_iff {A : ℕ → ℝ} (hA : rm2Conc A) (f : ℕ → ℝ) (hf0 : ∀ d, 0 ≤ f d)
    (hfs : Summable f) (p : ℝ) (y : ℕ) :
    Summable (fun d => f d * rm2Win A p d y) ↔ Summable (fun d => f d * rm2Win A p d 0) := by
  set K := ∑ w ∈ range y, (|p| + |A 1 - A 0| + |A (w + 1) - A w|)
  have hg : Summable (fun d => f d * (rm2Win A p d y - rm2Win A p d 0)) := by
    refine Summable.of_norm_bounded (hfs.mul_right K) (fun d => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf0 d)]
    exact mul_le_mul_of_nonneg_left (rm2Win_bound hA p d y) (hf0 d)
  constructor
  · intro h
    exact (h.sub hg).congr (fun d => by ring)
  · intro h
    exact (h.add hg).congr (fun d => by ring)

/-- The expected windowed maximum is concave (a non-summable expectation is `0` everywhere). -/
lemma rm2_tsum_conc {A : ℕ → ℝ} (hA : rm2Conc A) (f : ℕ → ℝ) (hf0 : ∀ d, 0 ≤ f d)
    (hfs : Summable f) (p : ℝ) : rm2Conc (fun y => ∑' d, f d * rm2Win A p d y) := by
  intro y
  by_cases hs : Summable (fun d => f d * rm2Win A p d 0)
  · have s0 := (rm2_summable_iff hA f hf0 hfs p y).2 hs
    have s1 := (rm2_summable_iff hA f hf0 hfs p (y + 1)).2 hs
    have s2 := (rm2_summable_iff hA f hf0 hfs p (y + 1 + 1)).2 hs
    simp only
    rw [← s2.tsum_sub s1, ← s1.tsum_sub s0]
    refine Summable.tsum_le_tsum (fun d => ?_) (s2.sub s1) (s1.sub s0)
    have := rm2Win_conc hA p d y
    have := hf0 d
    nlinarith
  · have z0 := tsum_eq_zero_of_not_summable (mt (rm2_summable_iff hA f hf0 hfs p y).1 hs)
    have z1 := tsum_eq_zero_of_not_summable (mt (rm2_summable_iff hA f hf0 hfs p (y + 1)).1 hs)
    have z2 := tsum_eq_zero_of_not_summable
      (mt (rm2_summable_iff hA f hf0 hfs p (y + 1 + 1)).1 hs)
    simp only [z0, z1, z2, le_refl, sub_self]

/-- One step of the window does not lose more than `p` where the objective does not decrease. -/
lemma rm2Win_step_lower (A : ℕ → ℝ) (p : ℝ) (d y : ℕ)
    (h : A y + (y : ℝ) * p ≤ A (y + 1) + ((y + 1 : ℕ) : ℝ) * p) :
    -p ≤ rm2Win A p d (y + 1) - rm2Win A p d y := by
  obtain ⟨x0, h1, h2, he⟩ := rm2Win_attained A p d y
  rw [he]
  rcases eq_or_lt_of_le h1 with hx | hx
  · subst hx
    have := rm2Win_ge A p d (y + 1) (y + 1) le_rfl (by omega)
    push_cast at this h ⊢
    linarith
  · have := rm2Win_ge A p d (y + 1) x0 (by omega) (by omega)
    push_cast at this ⊢
    linarith

/-! ### Concavity of the value functions (Sect. 4.3.1) -/

lemma rm2_term_conc (M : DynOverbooking) (hM : M.IsModel) (hc : IsConvexSeq M.c) :
    rm2Conc (M.valueGo 0) := by
  have hV : ∀ y, M.valueGo 0 y = if y ≤ M.C then 0 else -(M.c (y - M.C)) := fun y => rfl
  have hc0 := hM.2.2.2.2.1
  have hcn := hM.2.2.2.2.2
  intro z
  rw [hV, hV, hV]
  by_cases h1 : z + 1 + 1 ≤ M.C
  · rw [if_pos h1, if_pos (by omega), if_pos (by omega)]
  · by_cases h2 : z + 1 ≤ M.C
    · rw [if_neg h1, if_pos h2, if_pos (by omega)]
      have : z + 1 + 1 - M.C = 1 := by omega
      rw [this]
      have := hcn 1
      linarith
    · rw [if_neg h1, if_neg h2]
      have e1 : z + 1 + 1 - M.C = (z - M.C) + 1 + 1 := by omega
      have e2 : z + 1 - M.C = (z - M.C) + 1 := by omega
      have e3 : (if z ≤ M.C then (0 : ℝ) else -(M.c (z - M.C))) = -(M.c (z - M.C)) := by
        split_ifs with h3
        · have : z - M.C = 0 := by omega
          rw [this, hc0]; simp
        · rfl
      rw [e1, e2, e3]
      have := hc (z - M.C)
      linarith

lemma rm2_valueGo_conc (M : DynOverbooking) (hM : M.IsModel) (hc : IsConvexSeq M.c) :
    ∀ k, rm2Conc (M.valueGo k) := by
  intro k
  induction k with
  | zero => exact rm2_term_conc M hM hc
  | succ k ih =>
    have hq := hM.2.1 (M.T - k)
    have hA := rm2_post_conc hq.1 hq.2 (M.r (M.T - k)) ih
    exact rm2_tsum_conc hA (M.f (M.T - k)) (hM.1 (M.T - k)).1 (hM.1 (M.T - k)).2.summable
      (M.p (M.T - k))

lemma rm2_value_conc (M : DynOverbooking) (hM : M.IsModel) (hc : IsConvexSeq M.c) (t : ℕ) :
    rm2Conc (M.value t) :=
  rm2_valueGo_conc M hM hc (M.T + 1 - t)

lemma rm2_postValue_eq (M : DynOverbooking) (t x : ℕ) :
    M.postValue t x = rm2E (M.q t) (M.value (t + 1)) x - M.r t * (1 - M.q t) * x :=
  rm2_post_eq (M.q t) (M.r t) (M.value (t + 1)) x

lemma rm2_limit_conc (M : DynOverbooking) (hM : M.IsModel) (hc : IsConvexSeq M.c) (t : ℕ) :
    rm2Conc (M.limitObjective t) := by
  have hq := hM.2.1 t
  have hpost := rm2_post_conc hq.1 hq.2 (M.r t) (rm2_value_conc M hM hc (t + 1))
  intro x
  have := hpost x
  simp only [DynOverbooking.limitObjective, DynOverbooking.postValue] at this ⊢
  push_cast at this ⊢
  linarith

/-! ### The limit policy and the value increments -/

lemma rm2_policy_top (y d : ℕ) : limitPolicy ⊤ y d = y + d := by
  unfold limitPolicy
  rw [max_eq_right le_top, min_eq_left le_top, ENat.toNat_natCast]

lemma rm2_policy_coe (ℓ y d : ℕ) : limitPolicy (ℓ : ℕ∞) y d = min (y + d) (max y ℓ) := by
  unfold limitPolicy
  have hmax : max (y : ℕ∞) (ℓ : ℕ∞) = ((max y ℓ : ℕ) : ℕ∞) := by
    rcases le_total y ℓ with h | h
    · rw [max_eq_right (by exact_mod_cast h), max_eq_right h]
    · rw [max_eq_left (by exact_mod_cast h), max_eq_left h]
  rw [hmax]
  have hmin : min ((y + d : ℕ) : ℕ∞) ((max y ℓ : ℕ) : ℕ∞) = ((min (y + d) (max y ℓ) : ℕ) : ℕ∞) := by
    rcases le_total (y + d) (max y ℓ) with h | h
    · rw [min_eq_left (by exact_mod_cast h), min_eq_left h]
    · rw [min_eq_right (by exact_mod_cast h), min_eq_right h]
  rw [hmin, ENat.toNat_natCast]

/-- Where the objective of period `t + 1` does not decrease, the value of period `t + 1` loses at
most `p (t + 1)` per extra reservation (also when its expectation is not summable). -/
lemma rm2_value_step (M : DynOverbooking) (hM : M.IsModel) (hc : IsConvexSeq M.c) (t : ℕ)
    (htT : t < M.T) (z : ℕ)
    (hz : M.limitObjective (t + 1) z ≤ M.limitObjective (t + 1) (z + 1)) :
    -M.p (t + 1) ≤ M.value (t + 1) (z + 1) - M.value (t + 1) z := by
  set k := M.T - t - 1 with hk
  have hidx : M.T + 1 - (t + 1) = k + 1 := by omega
  have hTk : M.T - k = t + 1 := by omega
  have hidx2 : M.T + 1 - (t + 1 + 1) = k := by omega
  set A : ℕ → ℝ := fun x => ∑ w ∈ Finset.range (x + 1), binomPmf (M.q (t + 1)) x w *
      (M.valueGo k w - ((x : ℝ) - w) * M.r (t + 1)) with hA
  have hV : ∀ y, M.value (t + 1) y = ∑' d, M.f (t + 1) d * rm2Win A (M.p (t + 1)) d y := by
    intro y
    show M.valueGo (M.T + 1 - (t + 1)) y = _
    rw [hidx, DynOverbooking.valueGo.eq_2, hTk]
    rfl
  have hAc : rm2Conc A :=
    rm2_post_conc (hM.2.1 (t + 1)).1 (hM.2.1 (t + 1)).2 _ (rm2_valueGo_conc M hM hc k)
  have hval : ∀ w, M.value (t + 1 + 1) w = M.valueGo k w := fun w => by
    simp only [DynOverbooking.value, hidx2]
  have hGA : ∀ x, M.limitObjective (t + 1) x = A x + (x : ℝ) * M.p (t + 1) := by
    intro x
    simp only [DynOverbooking.limitObjective, DynOverbooking.postValue, hval, hA]
  have hstep : ∀ d, -M.p (t + 1) ≤ rm2Win A (M.p (t + 1)) d (z + 1) - rm2Win A (M.p (t + 1)) d z := by
    intro d
    apply rm2Win_step_lower
    rw [hGA, hGA] at hz
    exact hz
  rw [hV, hV]
  have hf := hM.1 (t + 1)
  have hp0 := hM.2.2.1 (t + 1)
  by_cases hs : Summable (fun d => M.f (t + 1) d * rm2Win A (M.p (t + 1)) d 0)
  · have s0 := (rm2_summable_iff hAc _ hf.1 hf.2.summable _ z).2 hs
    have s1 := (rm2_summable_iff hAc _ hf.1 hf.2.summable _ (z + 1)).2 hs
    rw [← s1.tsum_sub s0]
    have hfp : HasSum (fun d => M.f (t + 1) d * (-M.p (t + 1))) (1 * (-M.p (t + 1))) :=
      hf.2.mul_right _
    rw [one_mul] at hfp
    rw [← hfp.tsum_eq]
    refine Summable.tsum_le_tsum (fun d => ?_) hfp.summable (s1.sub s0)
    have := hstep d
    have := hf.1 d
    nlinarith
  · rw [tsum_eq_zero_of_not_summable
      (mt (rm2_summable_iff hAc _ hf.1 hf.2.summable _ (z + 1)).1 hs),
      tsum_eq_zero_of_not_summable (mt (rm2_summable_iff hAc _ hf.1 hf.2.summable _ z).1 hs)]
    linarith

end RevenueManagement

open RevenueManagement

theorem solution (M : DynOverbooking) (hM : M.IsModel) (hc : IsConvexSeq M.c)
    (t : ℕ) (ht : 1 ≤ t) (htT : t ≤ M.T) (y d : ℕ) :
    M.IsOptimalLevel t y d (limitPolicy (M.overbookingLimit t) y d) := by
  set G := M.limitObjective t with hGdef
  have hG : rm2Conc G := rm2_limit_conc M hM hc t
  have ha : ∀ z : ℕ, (z : ℕ∞) < M.overbookingLimit t → G z ≤ G (z + 1) :=
    fun z hz => rm2_enat_a G hG z hz
  have hb : ∀ z : ℕ, M.overbookingLimit t ≤ z → G (z + 1) < G z :=
    fun z hz => rm2_enat_b G hG z hz
  suffices H : y ≤ limitPolicy (M.overbookingLimit t) y d
      ∧ limitPolicy (M.overbookingLimit t) y d ≤ y + d
      ∧ ∀ x', y ≤ x' → x' ≤ y + d → G x' ≤ G (limitPolicy (M.overbookingLimit t) y d) by
    obtain ⟨h1, h2, h3⟩ := H
    refine ⟨h1, h2, fun x' hx1 hx2 => ?_⟩
    have := h3 x' hx1 hx2
    simp only [hGdef, DynOverbooking.limitObjective] at this
    linarith
  generalize hL : M.overbookingLimit t = L at ha hb ⊢
  induction L using ENat.recTopCoe with
  | top =>
    rw [rm2_policy_top]
    refine ⟨Nat.le_add_right _ _, le_rfl, fun x' _ h2 => ?_⟩
    exact rm2_mono_up G 0 (y + d) (fun z _ _ => ha z (ENat.natCast_lt_top z)) x' (y + d)
      (Nat.zero_le _) h2 le_rfl
  | coe ℓ =>
    rw [rm2_policy_coe]
    have ha' : ∀ z, z < ℓ → G z ≤ G (z + 1) := fun z hz => ha z (by exact_mod_cast hz)
    have hb' : ∀ z, ℓ ≤ z → G (z + 1) < G z := fun z hz => hb z (by exact_mod_cast hz)
    refine ⟨by omega, min_le_left _ _, fun x' h1 h2 => ?_⟩
    rcases le_or_gt ℓ y with hly | hly
    · rw [show min (y + d) (max y ℓ) = y by omega]
      exact rm2_mono_down G ℓ hb' y x' hly h1
    · rcases le_or_gt ℓ (y + d) with hl2 | hl2
      · rw [show min (y + d) (max y ℓ) = ℓ by omega]
        rcases le_total x' ℓ with h3 | h3
        · exact rm2_mono_up G 0 ℓ (fun z _ hz => ha' z hz) x' ℓ (Nat.zero_le _) h3 le_rfl
        · exact rm2_mono_down G ℓ hb' ℓ x' le_rfl h3
      · rw [show min (y + d) (max y ℓ) = y + d by omega]
        exact rm2_mono_up G 0 (y + d) (fun z _ hz => ha' z (by omega)) x' (y + d)
          (Nat.zero_le _) h2 le_rfl
