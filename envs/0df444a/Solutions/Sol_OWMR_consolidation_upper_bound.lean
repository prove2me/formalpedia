-- Prove2me | solution 1 for OWMR.consolidation_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T12:52:46.31463+00:00
-- url     : https://prove2.me/submissions/0d91c08d-e8f4-4de2-8009-854755a17c7b

import Theorems.Thm_OWMR_con_engine
import Theorems.Thm_OWMR_arb_credited_reserve
import Theorems.Thm_OWMR_con_offset_exists
import Theorems.Thm_OWMR_ss_poisson_upper_meas
import Theorems.Thm_OWMR_fifo_prep_bound
import Theorems.Thm_OWMR_F_properties
import Theorems.Thm_OWMR_con_retailer_budget
import Theorems.Thm_OWMR_arb_supplier_shortage
import Theorems.Thm_OWMR_arb_indep_max
import Theorems.Thm_OWMR_arb_protected_newsvendor
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Order.Filter.ENNReal
import Mathlib.Topology.Algebra.Order.LiminfLimsup

noncomputable section

section Part1

/-! Assembly, part 1: the explicit processes driving `π_con`. -/

open MeasureTheory
open scoped ENNReal NNReal


namespace OWMR.Asm

variable {n : ℕ} (N : Network n) (x : InitState n) (c : ConChoice n)

/-- Initial stock sent to the fixed retailer. -/
def W0 : ℝ := x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s

/-- Retailer inventory position before the start, after the demands of periods `< t`. -/
def IP (d : ℕ → DemandVec n) (t : ℕ) (i : Fin n) : ℝ :=
  x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
    + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0)
    - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ)

/-- The policy is running in period `t`. -/
def act (d : ℕ → DemandVec n) (t : ℕ) : Prop :=
  N.Tpipe - 1 + max 1 (N.L c.sendTo) ≤ t ∧ ∀ i,
      x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
        + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0)
        - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) ≤ c.S i

instance actDec (d : ℕ → DemandVec n) : DecidablePred (act N x c d) := fun _ => Classical.dec _

/-- Pre-order supplier position. -/
def Yp (d : ℕ → DemandVec n) : ℕ → ℝ
  | 0 => x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
      + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.S i)
  | t + 1 => (if act N x c d t ∧ Yp d t ≤ c.s0 then c.S0 else Yp d t) - ∑ i, ((d t i : ℝ≥0) : ℝ)

/-- Post-request retailer positions including outstanding requests. -/
def Ph (d : ℕ → DemandVec n) : ℕ → Fin n → ℝ
  | 0 => fun i => c.S i
  | t + 1 => fun i => if act N x c d t then
      (if Ph d t i - ((d t i : ℝ≥0) : ℝ) ≤ c.s i then c.S i else Ph d t i - ((d t i : ℝ≥0) : ℝ))
      else c.S i

/-- Request sizes. -/
def q (d : ℕ → DemandVec n) (t : ℕ) (i : Fin n) : ℝ :=
  if act N x c d t then
      (if t = 0 ∨ ¬ act N x c d (t - 1) then
        c.S i - (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
          + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0)
          - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ))
      else if Ph N x c d (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ) ≤ c.s i then
        c.S i - (Ph N x c d (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ)) else 0)
    else 0

/-- Cumulative allocation of the request of retailer `i` created in period `s`, after period `t`. -/
def A (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) (t : ℕ) : ℝ :=
  max 0 (min (q N x c d s i)
      (∑ r ∈ Finset.range (t + 1 - N.L0),
          (if act N x c d r ∧ Yp N x c d r ≤ c.s0 then c.S0 - Yp N x c d r else 0)
        - (∑ r ∈ Finset.range s, ∑ j, q N x c d r j
          + ∑ j ∈ Finset.univ.filter (· < i), q N x c d s j)))

/-- Supplier order. -/
def q0 (d : ℕ → DemandVec n) (r : ℕ) : ℝ :=
  if act N x c d r ∧ Yp N x c d r ≤ c.s0 then c.S0 - Yp N x c d r else 0

/-- Post-order supplier position. -/
def Ypost (d : ℕ → DemandVec n) (t : ℕ) : ℝ :=
  if act N x c d t ∧ Yp N x c d t ≤ c.s0 then c.S0 else Yp N x c d t

/-- Cumulative supplier arrivals by period `t`. -/
def V (d : ℕ → DemandVec n) (t : ℕ) : ℝ := ∑ r ∈ Finset.range (t + 1 - N.L0), q0 N x c d r

/-- Request volume ahead of request `(s, i)`. -/
def ahead (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) : ℝ :=
  ∑ r ∈ Finset.range s, ∑ j, q N x c d r j + ∑ j ∈ Finset.univ.filter (· < i), q N x c d s j

/-- Cumulative request volume through period `t`. -/
def Cq (d : ℕ → DemandVec n) (t : ℕ) : ℝ := ∑ r ∈ Finset.range (t + 1), ∑ j, q N x c d r j

/-- Total depletion. -/
def X (d : ℕ → DemandVec n) (t : ℕ) : ℝ := ∑ i, (c.S i - Ph N x c d t i)

lemma A_eq (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) (t : ℕ) :
    A N x c d s i t = max 0 (min (q N x c d s i) (V N x c d t - ahead N x c d s i)) := rfl

lemma Ypost_eq (d : ℕ → DemandVec n) (t : ℕ) : Ypost N x c d t = Yp N x c d t + q0 N x c d t := by
  unfold Ypost q0; split_ifs <;> ring

lemma Yp_succ (d : ℕ → DemandVec n) (t : ℕ) :
    Yp N x c d (t + 1) = Ypost N x c d t - ∑ i, ((d t i : ℝ≥0) : ℝ) := rfl

lemma L0_le_Tpipe : N.L0 ≤ N.Tpipe := le_max_left _ _

lemma L_le_Tpipe (i : Fin n) : N.L i ≤ N.Tpipe :=
  le_trans (Finset.le_sup (f := N.L) (Finset.mem_univ i)) (le_max_right _ _)

lemma act_time (d : ℕ → DemandVec n) (t : ℕ) (h : act N x c d t) :
    1 ≤ t ∧ N.L0 ≤ t ∧ N.Tpipe - 1 < t ∧ N.Tpipe - 1 + N.L c.sendTo ≤ t := by
  have h1 := h.1
  have h2 := L0_le_Tpipe N
  have h3 : 1 ≤ max 1 (N.L c.sendTo) := le_max_left _ _
  have h4 : N.L c.sendTo ≤ max 1 (N.L c.sendTo) := le_max_right _ _
  refine ⟨by omega, by omega, by omega, by omega⟩

lemma act_mono (d : ℕ → DemandVec n) (t : ℕ) (h : act N x c d t) : act N x c d (t + 1) := by
  refine ⟨by have := h.1; omega, fun i => ?_⟩
  have := h.2 i
  rw [Finset.sum_range_succ]
  linarith [NNReal.coe_nonneg (d t i)]

lemma act_mono' (d : ℕ → DemandVec n) {t t' : ℕ} (htt : t ≤ t') (h : act N x c d t) :
    act N x c d t' := by
  induction htt with
  | refl => exact h
  | step _ ih => exact act_mono N x c d _ ih

lemma not_act_zero (d : ℕ → DemandVec n) : ¬ act N x c d 0 := fun h =>
  absurd (act_time N x c d 0 h).1 (by omega)

lemma act_IP (d : ℕ → DemandVec n) (t : ℕ) (h : act N x c d t) (i : Fin n) :
    IP N x c d t i ≤ c.S i := h.2 i

lemma q_zero (d : ℕ → DemandVec n) (t : ℕ) (h : ¬ act N x c d t) (i : Fin n) :
    q N x c d t i = 0 := by
  unfold q; rw [if_neg h]

lemma q_nonneg (hsS : ∀ i, c.s i ≤ c.S i) (d : ℕ → DemandVec n) (t : ℕ) (i : Fin n) :
    0 ≤ q N x c d t i := by
  unfold q
  by_cases h1 : act N x c d t
  · rw [if_pos h1]
    by_cases h2 : t = 0 ∨ ¬ act N x c d (t - 1)
    · rw [if_pos h2]
      have := act_IP N x c d t h1 i
      unfold IP at this
      linarith
    · rw [if_neg h2]
      by_cases h3 : Ph N x c d (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ) ≤ c.s i
      · rw [if_pos h3]; linarith [hsS i]
      · rw [if_neg h3]
  · rw [if_neg h1]

lemma q_start (d : ℕ → DemandVec n) (t : ℕ) (h : act N x c d t) (h' : ¬ act N x c d (t - 1))
    (i : Fin n) : q N x c d t i = c.S i - IP N x c d t i := by
  unfold q; rw [if_pos h, if_pos (Or.inr h')]; rfl

lemma q_ord (d : ℕ → DemandVec n) (t : ℕ) (h : act N x c d t) (i : Fin n) :
    q N x c d (t + 1) i = if Ph N x c d t i - ((d t i : ℝ≥0) : ℝ) ≤ c.s i then
      c.S i - (Ph N x c d t i - ((d t i : ℝ≥0) : ℝ)) else 0 := by
  unfold q
  rw [if_pos (act_mono N x c d t h),
    if_neg (by simp only [add_tsub_cancel_right]; push Not; exact ⟨by omega, h⟩)]
  simp only [add_tsub_cancel_right]

lemma q0_zero (d : ℕ → DemandVec n) (t : ℕ) (h : ¬ act N x c d t) : q0 N x c d t = 0 := by
  unfold q0; rw [if_neg (fun h' => h h'.1)]

lemma q0_nonneg (hs0S : c.s0 ≤ c.S0) (d : ℕ → DemandVec n) (t : ℕ) : 0 ≤ q0 N x c d t := by
  unfold q0; split_ifs with h
  · linarith [h.2]
  · exact le_rfl

lemma Ph_bounds (hsS : ∀ i, c.s i ≤ c.S i) (d : ℕ → DemandVec n) :
    ∀ t i, c.s i ≤ Ph N x c d t i ∧ Ph N x c d t i ≤ c.S i
  | 0, i => ⟨hsS i, le_rfl⟩
  | t + 1, i => by
    have ih := Ph_bounds hsS d t i
    have hd := NNReal.coe_nonneg (d t i)
    simp only [Ph]
    split_ifs with h1 h2
    · exact ⟨hsS i, le_rfl⟩
    · exact ⟨by linarith [not_le.1 h2], by linarith⟩
    · exact ⟨hsS i, le_rfl⟩

/-- Before the start, the supplier position is the initial one minus demand. -/
lemma Yp_prep (d : ℕ → DemandVec n) : ∀ t, (∀ t' < t, ¬ act N x c d t') →
    Yp N x c d t = ∑ i, (IP N x c d t i - c.S i)
  | 0, _ => by
    simp only [Yp]
    unfold IP
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero]
    rw [Finset.sum_congr rfl (fun i _ => show x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
        + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0) - c.S i
      = (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.S i)
        + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0) by ring),
      Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ c.sendTo]
    simp only [Finset.mem_univ, if_true]
    ring
  | t + 1, h => by
    simp only [Yp]
    rw [if_neg (fun h' => h t (by omega) h'.1),
      Yp_prep d t (fun t' ht' => h t' (by omega))]
    unfold IP
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_range_succ]
    ring

/-- The supplier position accumulates orders and demand. -/
lemma Yp_cum (d : ℕ → DemandVec n) : ∀ t,
    Yp N x c d t = ∑ i, (IP N x c d 0 i - c.S i) + ∑ r ∈ Finset.range t, q0 N x c d r
      - ∑ r ∈ Finset.range t, ∑ i, ((d r i : ℝ≥0) : ℝ)
  | 0 => by
    rw [Yp_prep N x c d 0 (fun t' ht' => absurd ht' (Nat.not_lt_zero _))]
    simp
  | t + 1 => by
    rw [Yp_succ, Ypost_eq, Yp_cum d t, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

/-- Positions including outstanding requests, after the start. -/
lemma Ph_run (d : ℕ → DemandVec n) : ∀ t, act N x c d t → ∀ i,
    Ph N x c d t i = IP N x c d t i + ∑ r ∈ Finset.range (t + 1), q N x c d r i
  | 0, h, _ => absurd h (not_act_zero N x c d)
  | t + 1, h, i => by
    by_cases ht : act N x c d t
    · have ih := Ph_run d t ht i
      rw [Finset.sum_range_succ, q_ord N x c d t ht i]
      have hIP : IP N x c d (t + 1) i = IP N x c d t i - ((d t i : ℝ≥0) : ℝ) := by
        unfold IP; rw [Finset.sum_range_succ]; ring
      simp only [Ph, if_pos ht]
      rw [hIP]
      split_ifs with h1
      · linarith
      · linarith
    · -- the start period
      have hq0 : ∀ r ∈ Finset.range (t + 1), q N x c d r i = 0 := fun r hr =>
        q_zero N x c d r (fun h' => ht (act_mono' N x c d (by simp at hr; omega) h')) i
      rw [Finset.sum_range_succ, Finset.sum_eq_zero hq0,
        q_start N x c d (t + 1) h (by simpa using ht) i]
      simp only [Ph, if_neg ht]
      ring

lemma Cq_run (d : ℕ → DemandVec n) (t : ℕ) (h : act N x c d t) :
    Cq N x c d t = ∑ i, (Ph N x c d t i - IP N x c d t i) := by
  unfold Cq
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => by rw [Ph_run N x c d t h i]; ring

lemma IP_eq (d : ℕ → DemandVec n) (t : ℕ) (i : Fin n) :
    IP N x c d t i = IP N x c d 0 i - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) := by
  unfold IP; simp

/-- The key identity: cumulative orders minus cumulative requests. -/
lemma key_id (d : ℕ → DemandVec n) (t : ℕ) (h : act N x c d t) :
    ∑ r ∈ Finset.range (t + 1), q0 N x c d r - Cq N x c d t
      = Ypost N x c d t + X N x c d t := by
  rw [Cq_run N x c d t h, Finset.sum_range_succ, Ypost_eq, Yp_cum N x c d t]
  unfold X
  have e : ∑ r ∈ Finset.range t, ∑ i, ((d r i : ℝ≥0) : ℝ)
      = ∑ i, ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ) := Finset.sum_comm
  simp only [IP_eq N x c d t]
  rw [e]
  simp only [Finset.sum_sub_distrib]
  ring

lemma X_nonneg (hsS : ∀ i, c.s i ≤ c.S i) (d : ℕ → DemandVec n) (t : ℕ) : 0 ≤ X N x c d t :=
  Finset.sum_nonneg fun i _ => sub_nonneg.2 (Ph_bounds N x c hsS d t i).2

lemma Ypost_nonneg (hs0 : 0 ≤ c.s0) (hs0S : c.s0 ≤ c.S0) (d : ℕ → DemandVec n) (t : ℕ)
    (h : act N x c d t) : 0 ≤ Ypost N x c d t := by
  unfold Ypost
  split_ifs with h1
  · linarith
  · push Not at h1
    linarith [h1 h]

lemma V_mono (hs0S : c.s0 ≤ c.S0) (d : ℕ → DemandVec n) {t t' : ℕ} (htt : t ≤ t') :
    V N x c d t ≤ V N x c d t' :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
    fun r _ _ => q0_nonneg N x c hs0S d r

lemma V_nonneg (hs0S : c.s0 ≤ c.S0) (d : ℕ → DemandVec n) (t : ℕ) : 0 ≤ V N x c d t :=
  Finset.sum_nonneg fun r _ => q0_nonneg N x c hs0S d r

lemma Cq_le_V (hsS : ∀ i, c.s i ≤ c.S i) (hs0 : 0 ≤ c.s0) (hs0S : c.s0 ≤ c.S0)
    (d : ℕ → DemandVec n) (s t : ℕ) (hs : act N x c d s) (hst : s + N.L0 ≤ t) :
    Cq N x c d s ≤ V N x c d t := by
  have h1 : V N x c d (s + N.L0) = ∑ r ∈ Finset.range (s + 1), q0 N x c d r := by
    unfold V; rw [show s + N.L0 + 1 - N.L0 = s + 1 by omega]
  have h2 := key_id N x c d s hs
  have h3 := Ypost_nonneg N x c hs0 hs0S d s hs
  have h4 := X_nonneg N x c hsS d s
  have h5 := V_mono N x c hs0S d hst
  linarith

lemma ahead_nonneg (hsS : ∀ i, c.s i ≤ c.S i) (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) :
    0 ≤ ahead N x c d s i :=
  add_nonneg (Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun j _ => q_nonneg N x c hsS d r j)
    (Finset.sum_nonneg fun j _ => q_nonneg N x c hsS d s j)

lemma ahead_add_le_Cq (hsS : ∀ i, c.s i ≤ c.S i) (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) :
    ahead N x c d s i + q N x c d s i ≤ Cq N x c d s := by
  unfold ahead Cq
  rw [Finset.sum_range_succ, add_assoc]
  gcongr
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· < i)]
  gcongr
  calc q N x c d s i = ∑ j ∈ {i}, q N x c d s j := by simp
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (by intro j hj; simp at hj; simp [hj])
        fun j _ _ => q_nonneg N x c hsS d s j

lemma ahead_mono (hsS : ∀ i, c.s i ≤ c.S i) (d : ℕ → DemandVec n) (r r' : ℕ) (i i' : Fin n)
    (h : r < r' ∨ (r = r' ∧ i < i')) :
    ahead N x c d r i + q N x c d r i ≤ ahead N x c d r' i' := by
  rcases h with h | ⟨rfl, h⟩
  · calc ahead N x c d r i + q N x c d r i ≤ Cq N x c d r := ahead_add_le_Cq N x c hsS d r i
      _ = ∑ r'' ∈ Finset.range (r + 1), ∑ j, q N x c d r'' j := rfl
      _ ≤ ∑ r'' ∈ Finset.range r', ∑ j, q N x c d r'' j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 h)
            fun r'' _ _ => Finset.sum_nonneg fun j _ => q_nonneg N x c hsS d r'' j
      _ ≤ ahead N x c d r' i' := le_add_of_nonneg_right
          (Finset.sum_nonneg fun j _ => q_nonneg N x c hsS d r' j)
  · unfold ahead
    rw [add_assoc]
    gcongr
    have hsub : Finset.univ.filter (· < i) ∪ {i} ⊆ Finset.univ.filter (· < i') := by
      intro j hj
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton] at hj ⊢
      rcases hj with hj | rfl
      · exact lt_trans hj h
      · exact h
    calc ∑ j ∈ Finset.univ.filter (· < i), q N x c d r j + q N x c d r i
        = ∑ j ∈ Finset.univ.filter (· < i) ∪ {i}, q N x c d r j := by
          rw [Finset.sum_union (by simp)]; simp
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => q_nonneg N x c hsS d r j

lemma A_nonneg (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) (t : ℕ) : 0 ≤ A N x c d s i t :=
  le_max_left _ _

lemma A_le_q (hsS : ∀ i, c.s i ≤ c.S i) (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) (t : ℕ) :
    A N x c d s i t ≤ q N x c d s i := by
  rw [A_eq]; exact max_le (q_nonneg N x c hsS d s i) (min_le_left _ _)

lemma A_mono (hs0S : c.s0 ≤ c.S0) (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) {t t' : ℕ}
    (htt : t ≤ t') : A N x c d s i t ≤ A N x c d s i t' := by
  rw [A_eq, A_eq]
  have := V_mono N x c hs0S d htt
  exact max_le_max le_rfl (min_le_min le_rfl (by linarith))

lemma A_full (hsS : ∀ i, c.s i ≤ c.S i) (hs0 : 0 ≤ c.s0) (hs0S : c.s0 ≤ c.S0)
    (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) (t : ℕ) (hs : act N x c d s) (hst : s + N.L0 ≤ t) :
    A N x c d s i t = q N x c d s i := by
  rw [A_eq]
  have h1 := Cq_le_V N x c hsS hs0 hs0S d s t hs hst
  have h2 := ahead_add_le_Cq N x c hsS d s i
  rw [min_eq_left (by linarith), max_eq_right (q_nonneg N x c hsS d s i)]

lemma A_zero (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) (t : ℕ) (hs : ¬ act N x c d s) :
    A N x c d s i t = 0 := by
  rw [A_eq, q_zero N x c d s hs]; simp

/-- At most one request is partially allocated in each period. -/
lemma partial_unique (hsS : ∀ i, c.s i ≤ c.S i) (d : ℕ → DemandVec n) (t r r' : ℕ) (i i' : Fin n)
    (h1 : 0 < A N x c d r i t ∧ A N x c d r i t < q N x c d r i)
    (h2 : 0 < A N x c d r' i' t ∧ A N x c d r' i' t < q N x c d r' i') : r = r' ∧ i = i' := by
  have key : ∀ r r' : ℕ, ∀ i i' : Fin n, (r < r' ∨ (r = r' ∧ i < i')) →
      0 < A N x c d r i t → A N x c d r i t < q N x c d r i → A N x c d r' i' t ≤ 0 := by
    intro r r' i i' hlt ha hb
    have hm := ahead_mono N x c hsS d r r' i i' hlt
    rw [A_eq] at ha hb ⊢
    have hv : V N x c d t - ahead N x c d r i < q N x c d r i := by
      by_contra hc
      push Not at hc
      rw [min_eq_left hc, max_eq_right (q_nonneg N x c hsS d r i)] at hb
      exact lt_irrefl _ hb
    exact max_le le_rfl (le_trans (min_le_right _ _) (by linarith))
  rcases lt_trichotomy r r' with hr | hr | hr
  · exact absurd (key r r' i i' (Or.inl hr) h1.1 h1.2) (not_le.2 h2.1)
  · subst hr
    rcases lt_trichotomy i i' with hi | hi | hi
    · exact absurd (key r r i i' (Or.inr ⟨rfl, hi⟩) h1.1 h1.2) (not_le.2 h2.1)
    · exact ⟨rfl, hi⟩
    · exact absurd (key r r i' i (Or.inr ⟨rfl, hi⟩) h2.1 h2.2) (not_le.2 h1.1)
  · exact absurd (key r' r i' i (Or.inl hr) h2.1 h2.2) (not_le.2 h1.1)

/-- Clamped allocation as a difference of a monotone level. -/
lemma clamp_diff (a qq v : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ qq) :
    max 0 (min qq (v - a)) = max 0 (min v (a + qq)) - max 0 (min v a) := by
  rcases le_or_gt v a with h | h
  · rw [min_eq_left (by linarith : v ≤ a + qq), min_eq_left h]
    rw [max_eq_left (min_le_of_right_le (by linarith : v - a ≤ 0))]
    ring
  · rcases le_or_gt v (a + qq) with h' | h'
    · rw [min_eq_right (by linarith : v - a ≤ qq), min_eq_left h', min_eq_right h.le,
        max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right ha]
    · rw [min_eq_left (by linarith : qq ≤ v - a), min_eq_right h'.le, min_eq_right h.le,
        max_eq_right hq, max_eq_right (by linarith), max_eq_right ha]
      ring

/-- Telescoping over retailers in index order. -/
lemma fin_telescope (f : ℝ → ℝ) (qq : Fin n → ℝ) :
    ∑ i, (f (∑ j ∈ Finset.univ.filter (· < i), qq j + qq i)
        - f (∑ j ∈ Finset.univ.filter (· < i), qq j)) = f (∑ j, qq j) - f 0 := by
  set q' : ℕ → ℝ := fun k => if h : k < n then qq ⟨k, h⟩ else 0 with hq'
  have hq'i : ∀ i : Fin n, qq i = q' i := fun i => by simp [hq', i.2]
  have hpre : ∀ i : Fin n, ∑ j ∈ Finset.univ.filter (· < i), qq j
      = ∑ k ∈ Finset.range i.val, q' k := by
    intro i
    rw [Finset.sum_filter]
    have e : ∀ j : Fin n, (if j < i then qq j else 0)
        = (fun k : ℕ => if k < i.val then q' k else 0) j := fun j => by
      by_cases h : j < i
      · rw [if_pos h]; simp only; rw [if_pos (Fin.lt_iff_val_lt_val.1 h), hq'i]
      · rw [if_neg h]; simp only; rw [if_neg (fun h' => h (Fin.lt_iff_val_lt_val.2 h'))]
    rw [Finset.sum_congr rfl (fun j _ => e j),
      Fin.sum_univ_eq_sum_range (fun k => if k < i.val then q' k else 0) n, ← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨lt_trans h i.2, h⟩⟩
  have hall : ∑ j, qq j = ∑ k ∈ Finset.range n, q' k := by
    rw [Finset.sum_congr rfl (fun j _ => hq'i j), Fin.sum_univ_eq_sum_range q' n]
  set G : ℕ → ℝ := fun k => f (∑ k' ∈ Finset.range k, q' k' + q' k)
    - f (∑ k' ∈ Finset.range k, q' k') with hG
  have e2 : ∀ i : Fin n, f (∑ j ∈ Finset.univ.filter (· < i), qq j + qq i)
      - f (∑ j ∈ Finset.univ.filter (· < i), qq j) = G i := fun i => by
    rw [hpre i, hq'i i]
  rw [Finset.sum_congr rfl (fun i _ => e2 i), Fin.sum_univ_eq_sum_range G n, hall]
  rw [show (0 : ℝ) = ∑ k' ∈ Finset.range 0, q' k' by simp]
  rw [← Finset.sum_range_sub (fun k => f (∑ k' ∈ Finset.range k, q' k'))]
  exact Finset.sum_congr rfl fun k _ => by rw [hG, Finset.sum_range_succ]

/-- Total allocated volume. -/
lemma sum_A (hsS : ∀ i, c.s i ≤ c.S i) (d : ℕ → DemandVec n) (t : ℕ) :
    ∑ r ∈ Finset.range (t + 1), ∑ i, A N x c d r i t
      = max 0 (min (V N x c d t) (Cq N x c d t)) := by
  set φ : ℝ → ℝ := fun z => max 0 (min (V N x c d t) z) with hφ
  set B : ℕ → ℝ := fun r => ∑ r' ∈ Finset.range r, ∑ j, q N x c d r' j with hB
  have hstep : ∀ r, ∑ i, A N x c d r i t = φ (B (r + 1)) - φ (B r) := by
    intro r
    have e1 : ∀ i, A N x c d r i t = φ (ahead N x c d r i + q N x c d r i)
        - φ (ahead N x c d r i) := fun i => by
      rw [A_eq]
      exact clamp_diff _ _ _ (ahead_nonneg N x c hsS d r i) (q_nonneg N x c hsS d r i)
    simp_rw [e1]
    have := fin_telescope (fun z => φ (B r + z)) (fun j => q N x c d r j)
    simp only [add_zero] at this
    have e2 : ∀ i, ahead N x c d r i = B r + ∑ j ∈ Finset.univ.filter (· < i), q N x c d r j :=
      fun i => rfl
    simp_rw [e2, add_assoc]
    rw [this, hB]
    simp only [Finset.sum_range_succ]
  simp_rw [hstep]
  rw [Finset.sum_range_sub (fun r => φ (B r))]
  simp only [hφ, hB, Finset.range_zero, Finset.sum_empty]
  rw [show min (V N x c d t) 0 = min (V N x c d t) 0 from rfl]
  have : max 0 (min (V N x c d t) (0 : ℝ)) = 0 := by
    rcases le_total (V N x c d t) 0 with h | h
    · rw [min_eq_left h, max_eq_left h]
    · rw [min_eq_right h, max_self]
  rw [this, sub_zero]
  rfl

end OWMR.Asm

end Part1

section Part2

/-! Assembly, part 2: decisions of `π_con`, shipments and physical quantities. -/

open MeasureTheory
open scoped ENNReal NNReal


namespace OWMR.Asm

variable {n : ℕ} (N : Network n) (x : InitState n) (c : ConChoice n)

/-- The engine applied to the explicit processes. -/
lemma engine (hsS : ∀ i, c.s i ≤ c.S i) (hs0S : c.s0 ≤ c.S0)
    (hθ0 : ∀ i, 0 < c.initOffset i ∧ c.initOffset i < 1) :
    ∃ θ : (ℕ → DemandVec n) → ℕ → Fin n → ℝ,
      (∀ d s i, 0 < θ d s i ∧ θ d s i < 1) ∧
      (∀ d d' s, (∀ r < s, d r = d' r) → ∀ i, θ d s i = θ d' s i) ∧
      (∀ d t, (conPolicy N x c).order t d = q0 N x c d t) ∧
      (∀ d t i, (conPolicy N x c).dispatch t d i = if act N x c d t then
        ∑ s ∈ Finset.range (t + 1),
          ((if c.batch i then shippedPath (q N x c d s i) (θ d s i)
                (fun k => A N x c d s i (s + k)) (t - s)
              else A N x c d s i t)
            - if s < t then (if c.batch i then
                shippedPath (q N x c d s i) (θ d s i) (fun k => A N x c d s i (s + k)) (t - 1 - s)
              else A N x c d s i (t - 1)) else 0)
        else if t = N.Tpipe - 1 ∧ i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
        else 0) ∧
      (∀ d s i, 0 < s → act N x c d (s - 1) → 0 < q N x c d s i → c.batch i = true →
        ∃ σ : EngState n,
          θ d s i = conRule N c σ s (∑ r ∈ Finset.range s,
              (if 0 < r ∧ act N x c d (r - 1) then
                ((List.finRange n).filter (fun j => decide (0 < q N x c d r j))).length else 0)
            + ((List.finRange n).filter (fun j => decide (0 < q N x c d s j))).idxOf i + 1) i
              (q N x c d s i) ∧
          ∀ (ds : Fin N.L0 → DemandVec n) (k : ℕ), k ≤ N.L0 →
            idealAlloc N c.params σ s i (q N x c d s i) (padHist N.L0 ds) k = A N x c d s i (s + k) ∧
            idealDepletion N c.params σ s (padHist N.L0 ds) k
              = ∑ j, (c.S j - Ph N x c (fun r => if r < s then d r else padHist N.L0 ds (r - s))
                  (s + k) j)) := by
  obtain ⟨θ, h1, h2, h3, h4, h5⟩ := con_engine N x c hsS hs0S hθ0 (act N x c)
    (fun d t => Iff.rfl) (Yp N x c) (fun d => rfl) (fun d t => rfl) (Ph N x c) (fun d i => rfl)
    (fun d t i => rfl) (q N x c) (fun d t i => rfl) (A N x c) (fun d s i t => rfl)
  exact ⟨θ, h1, h2, fun d t => h3 d t, h4, h5⟩

lemma ship_zero_path (Q θ' : ℝ) (A' : ℕ → ℝ) (h : ∀ k, A' k = 0) :
    ∀ k, shippedPath Q θ' A' k = 0
  | 0 => by simp only [shippedPath, h 0]; split_ifs <;> rfl
  | k + 1 => by
    simp only [shippedPath, h (k + 1), ship_zero_path Q θ' A' h k]; split_ifs <;> rfl

section ship

variable (θ : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)

/-- Quantity of request `(s, i)` shipped by the end of period `t`. -/
def sh (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) (t : ℕ) : ℝ :=
  if c.batch i then shippedPath (q N x c d s i) (θ d s i) (fun k => A N x c d s i (s + k)) (t - s)
  else A N x c d s i t

lemma sh_zero (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) (t : ℕ) (hs : ¬ act N x c d s) :
    sh N x c θ d s i t = 0 := by
  unfold sh
  split_ifs
  · exact ship_zero_path _ _ _ (fun k => A_zero N x c d s i _ hs) _
  · exact A_zero N x c d s i t hs

lemma sh_props (hsS : ∀ i, c.s i ≤ c.S i) (hs0S : c.s0 ≤ c.S0) (d : ℕ → DemandVec n) (s : ℕ)
    (i : Fin n) (t : ℕ) (hst : s ≤ t) :
    0 ≤ sh N x c θ d s i t ∧ sh N x c θ d s i t ≤ A N x c d s i t ∧
      (A N x c d s i t = q N x c d s i → sh N x c θ d s i t = q N x c d s i) := by
  unfold sh
  split_ifs with hb
  · rcases eq_or_lt_of_le (q_nonneg N x c hsS d s i) with hq | hq
    · have hA : ∀ k, A N x c d s i (s + k) = 0 := fun k =>
        le_antisymm (by rw [hq]; exact A_le_q N x c hsS d s i _) (A_nonneg N x c d s i _)
      rw [ship_zero_path _ _ _ hA]
      refine ⟨le_rfl, A_nonneg N x c d s i t, fun _ => hq⟩
    · obtain ⟨c1, c2, -, -, -⟩ := arb_credited_reserve (q N x c d s i)
        (fun k => A N x c d s i (s + k)) hq (A_nonneg N x c d s i _)
        (fun k k' hk => A_mono N x c hs0S d s i (by omega)) (fun k => A_le_q N x c hsS d s i _)
      have e : s + (t - s) = t := by omega
      refine ⟨(c1 (θ d s i) (t - s)).1, ?_, fun h => ?_⟩
      · have := (c1 (θ d s i) (t - s)).2; simp only [e] at this; exact this
      · exact c2 (θ d s i) (t - s) (by simp only [e]; exact h)
  · exact ⟨A_nonneg N x c d s i t, le_rfl, id⟩

variable (hdisp : ∀ d t i, (conPolicy N x c).dispatch t d i = if act N x c d t then
        ∑ s ∈ Finset.range (t + 1),
          ((if c.batch i then shippedPath (q N x c d s i) (θ d s i)
                (fun k => A N x c d s i (s + k)) (t - s)
              else A N x c d s i t)
            - if s < t then (if c.batch i then
                shippedPath (q N x c d s i) (θ d s i) (fun k => A N x c d s i (s + k)) (t - 1 - s)
              else A N x c d s i (t - 1)) else 0)
        else if t = N.Tpipe - 1 ∧ i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
        else 0)

include hdisp in
lemma disp_run (d : ℕ → DemandVec n) (t : ℕ) (i : Fin n) (h : act N x c d t) :
    (conPolicy N x c).dispatch t d i = ∑ s ∈ Finset.range (t + 1),
      (sh N x c θ d s i t - if s < t then sh N x c θ d s i (t - 1) else 0) := by
  rw [hdisp, if_pos h]; rfl

include hdisp in
lemma disp_prep (d : ℕ → DemandVec n) (t : ℕ) (i : Fin n) (h : ¬ act N x c d t) :
    (conPolicy N x c).dispatch t d i = if t = N.Tpipe - 1 ∧ i = c.sendTo then W0 N x else 0 := by
  rw [hdisp, if_neg h]; rfl

include hdisp in
/-- Cumulative dispatches. -/
lemma cum_disp (d : ℕ → DemandVec n) (i : Fin n) : ∀ t,
    ∑ s ∈ Finset.range (t + 1), (conPolicy N x c).dispatch s d i
      = (if N.Tpipe - 1 ≤ t ∧ i = c.sendTo then W0 N x else 0)
        + ∑ r ∈ Finset.range (t + 1), sh N x c θ d r i t
  | 0 => by
    rw [Finset.sum_range_one, Finset.sum_range_one, disp_prep N x c θ hdisp d 0 i
      (not_act_zero N x c d), sh_zero N x c θ d 0 i 0 (not_act_zero N x c d), add_zero]
    by_cases h : N.Tpipe - 1 = 0 ∧ i = c.sendTo
    · rw [if_pos ⟨h.1.symm, h.2⟩, if_pos ⟨by omega, h.2⟩]
    · rw [if_neg (fun h' => h ⟨h'.1.symm, h'.2⟩), if_neg (fun h' => h ⟨by omega, h'.2⟩)]
  | t + 1 => by
    rw [Finset.sum_range_succ, cum_disp d i t]
    by_cases ha : act N x c d (t + 1)
    · rw [disp_run N x c θ hdisp d (t + 1) i ha]
      have ht := (act_time N x c d (t + 1) ha).2.2.1
      have e1 : (if N.Tpipe - 1 ≤ t ∧ i = c.sendTo then W0 N x else 0)
          = (if N.Tpipe - 1 ≤ t + 1 ∧ i = c.sendTo then W0 N x else 0) := by
        by_cases hi : i = c.sendTo
        · rw [if_pos ⟨by omega, hi⟩, if_pos ⟨by omega, hi⟩]
        · rw [if_neg (fun h => hi h.2), if_neg (fun h => hi h.2)]
      rw [e1, Finset.sum_sub_distrib, Finset.sum_range_succ (fun s => if s < t + 1 then _ else _)]
      simp only [lt_irrefl, if_false, add_zero, add_tsub_cancel_right]
      rw [Finset.sum_congr rfl (fun s hs => if_pos (Finset.mem_range.1 hs))]
      ring
    · rw [disp_prep N x c θ hdisp d (t + 1) i ha]
      have hz : ∀ t' ≤ t + 1, ∀ r ∈ Finset.range (t' + 1), sh N x c θ d r i t' = 0 :=
        fun t' ht' r hr => sh_zero N x c θ d r i t' (fun h' => ha (act_mono' N x c d
          (by simp at hr; omega) h'))
      rw [Finset.sum_eq_zero (hz t (by omega)), Finset.sum_eq_zero (hz (t + 1) le_rfl)]
      by_cases hi : i = c.sendTo
      · by_cases h1 : N.Tpipe - 1 ≤ t
        · rw [if_pos (show N.Tpipe - 1 ≤ t ∧ i = c.sendTo from ⟨h1, hi⟩),
            if_pos (show N.Tpipe - 1 ≤ t + 1 ∧ i = c.sendTo from ⟨by omega, hi⟩),
            if_neg (show ¬ (t + 1 = N.Tpipe - 1 ∧ i = c.sendTo) from fun h => by omega)]
          ring
        · by_cases h2 : t + 1 = N.Tpipe - 1
          · rw [if_neg (show ¬ (N.Tpipe - 1 ≤ t ∧ i = c.sendTo) from fun h => h1 h.1),
              if_pos (show t + 1 = N.Tpipe - 1 ∧ i = c.sendTo from ⟨h2, hi⟩),
              if_pos (show N.Tpipe - 1 ≤ t + 1 ∧ i = c.sendTo from ⟨by omega, hi⟩)]
            ring
          · rw [if_neg (show ¬ (N.Tpipe - 1 ≤ t ∧ i = c.sendTo) from fun h => h1 h.1),
              if_neg (show ¬ (t + 1 = N.Tpipe - 1 ∧ i = c.sendTo) from fun h => h2 h.1),
              if_neg (show ¬ (N.Tpipe - 1 ≤ t + 1 ∧ i = c.sendTo) from fun h => by omega)]
            ring
      · rw [if_neg (show ¬ (N.Tpipe - 1 ≤ t ∧ i = c.sendTo) from fun h => hi h.2),
          if_neg (show ¬ (t + 1 = N.Tpipe - 1 ∧ i = c.sendTo) from fun h => hi h.2),
          if_neg (show ¬ (N.Tpipe - 1 ≤ t + 1 ∧ i = c.sendTo) from fun h => hi h.2)]
        ring

end ship

/-- Retailer holding and backlog loss. -/
def cH (i : Fin n) (y : ℝ) : ℝ := N.H i * max y 0 + N.p * max (-y) 0

/-- Retailer physical position after the dispatches of period `t`. -/
def rP (d : ℕ → DemandVec n) (t : ℕ) (i : Fin n) : ℝ :=
  x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
    + ∑ r ∈ Finset.range (t + 1), (conPolicy N x c).dispatch r d i
    - ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ)

lemma netInv_shift (d : ℕ → DemandVec n) (i : Fin n) (t : ℕ) :
    Policy.netInv N x (conPolicy N x c).toPolicy () d i (t + N.L i)
      = rP N x c d t i - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ) := by
  unfold Policy.netInv rP
  rw [Finset.sum_sub_distrib]
  have h1 : ∑ s ∈ Finset.range (t + N.L i + 1),
        Policy.retArrival N x (conPolicy N x c).toPolicy () d i s
      = ∑ s ∈ Finset.range (N.L i), x.retPipe i s
        + ∑ r ∈ Finset.range (t + 1), (conPolicy N x c).dispatch r d i := by
    rw [show t + N.L i + 1 = N.L i + (t + 1) by omega, Finset.sum_range_add]
    congr 1
    · exact Finset.sum_congr rfl fun s hs => by
        simp only [Policy.retArrival, if_pos (Finset.mem_range.1 hs)]
    · exact Finset.sum_congr rfl fun r _ => by
        simp only [Policy.retArrival, if_neg (show ¬(N.L i + r < N.L i) by omega),
          Nat.add_sub_cancel_left]
        rfl
  have h2 : ∑ s ∈ Finset.range (t + N.L i + 1), ((d s i : ℝ≥0) : ℝ)
      = ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ)
        + ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ) := by
    rw [show t + N.L i + 1 = t + (N.L i + 1) by omega, Finset.sum_range_add]
  rw [h1, h2]
  ring

lemma cH_nonneg (hN : N.Standing) (i : Fin n) (y : ℝ) : 0 ≤ cH N i y :=
  add_nonneg (mul_nonneg (hN.H_pos i).le (le_max_right _ _))
    (mul_nonneg hN.p_pos.le (le_max_right _ _))

lemma cH_slope (hN : N.Standing) (i : Fin n) (y y' : ℝ) (hy : y ≤ y') :
    cH N i y ≤ cH N i y' + N.p * (y' - y) := by
  unfold cH
  have hH := (hN.H_pos i).le
  have hp := hN.p_pos.le
  have h1 : max y 0 ≤ max y' 0 := max_le_max hy le_rfl
  have h2 : max (-y) 0 ≤ max (-y') 0 + (y' - y) := by
    rcases le_total (-y') 0 with h | h
    · rw [max_eq_right h]; exact max_le (by linarith) (by linarith)
    · rw [max_eq_left h]; exact max_le (by linarith) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left h1 hH, mul_le_mul_of_nonneg_left h2 hp]

lemma whLoss_add_le (h p a b : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) (hb : 0 ≤ b) :
    whLoss h p (a + b) ≤ whLoss h p a + h * b := by
  unfold whLoss
  have h1 : max (a + b) 0 ≤ max a 0 + b :=
    max_le (by linarith [le_max_left a 0]) (by linarith [le_max_right a 0])
  have h2 : max (-(a + b)) 0 ≤ max (-a) 0 := max_le_max (by linarith) le_rfl
  nlinarith [mul_le_mul_of_nonneg_left h1 hh, mul_le_mul_of_nonneg_left h2 hp]

lemma whLoss_nonneg (h p y : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) : 0 ≤ whLoss h p y :=
  add_nonneg (mul_nonneg hh (le_max_right _ _)) (mul_nonneg hp (le_max_right _ _))

section ship2

variable (θ : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)
  (hdisp : ∀ d t i, (conPolicy N x c).dispatch t d i = if act N x c d t then
        ∑ s ∈ Finset.range (t + 1),
          ((if c.batch i then shippedPath (q N x c d s i) (θ d s i)
                (fun k => A N x c d s i (s + k)) (t - s)
              else A N x c d s i t)
            - if s < t then (if c.batch i then
                shippedPath (q N x c d s i) (θ d s i) (fun k => A N x c d s i (s + k)) (t - 1 - s)
              else A N x c d s i (t - 1)) else 0)
        else if t = N.Tpipe - 1 ∧ i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
        else 0)
  (hord : ∀ d t, (conPolicy N x c).order t d = q0 N x c d t)

include hord in
lemma cum_sup (d : ℕ → DemandVec n) (t : ℕ) :
    ∑ s ∈ Finset.range (t + 1), Policy.supArrival N x (conPolicy N x c).toPolicy () d s
      = ∑ s ∈ Finset.range (min (t + 1) N.L0), x.supPipe s + V N x c d t := by
  unfold V
  rcases le_or_gt (t + 1) N.L0 with h | h
  · rw [min_eq_left h, show t + 1 - N.L0 = 0 by omega, Finset.range_zero, Finset.sum_empty,
      add_zero]
    exact Finset.sum_congr rfl fun s hs => by
      simp only [Policy.supArrival, if_pos (show s < N.L0 by simp at hs; omega)]
  · rw [min_eq_right h.le, ← Finset.sum_range_add_sum_Ico _ h.le, Finset.sum_Ico_eq_sum_range]
    congr 1
    · exact Finset.sum_congr rfl fun s hs => by
        simp only [Policy.supArrival, if_pos (Finset.mem_range.1 hs)]
    · exact Finset.sum_congr rfl fun r _ => by
        simp only [Policy.supArrival, if_neg (show ¬(N.L0 + r < N.L0) by omega),
          Nat.add_sub_cancel_left]
        exact hord d r

include hdisp hord in
lemma whStock_eq (d : ℕ → DemandVec n) (t : ℕ) :
    Policy.whStock N x (conPolicy N x c).toPolicy () d t
      = x.W + ∑ s ∈ Finset.range (min (t + 1) N.L0), x.supPipe s + V N x c d t
        - (if N.Tpipe - 1 ≤ t then W0 N x else 0)
        - ∑ r ∈ Finset.range (t + 1), ∑ i, sh N x c θ d r i t := by
  unfold Policy.whStock
  rw [Finset.sum_sub_distrib, cum_sup N x c hord d t]
  have e1 : ∑ s ∈ Finset.range (t + 1), ∑ i, (conPolicy N x c).toPolicy.dispatch s () d i
      = ∑ i, ∑ s ∈ Finset.range (t + 1), (conPolicy N x c).dispatch s d i := Finset.sum_comm
  rw [e1]
  simp_rw [cum_disp N x c θ hdisp d]
  rw [Finset.sum_add_distrib, Finset.sum_comm (s := Finset.univ)]
  have e2 : ∑ i : Fin n, (if N.Tpipe - 1 ≤ t ∧ i = c.sendTo then W0 N x else 0)
      = if N.Tpipe - 1 ≤ t then W0 N x else 0 := by
    by_cases h : N.Tpipe - 1 ≤ t
    · simp [h]
    · simp [h]
  rw [e2]
  ring

include hdisp hord in
lemma whStock_run (d : ℕ → DemandVec n) (t : ℕ) (h : act N x c d t) :
    Policy.whStock N x (conPolicy N x c).toPolicy () d t
      = V N x c d t - ∑ r ∈ Finset.range (t + 1), ∑ i, sh N x c θ d r i t := by
  rw [whStock_eq N x c θ hdisp hord d t]
  have ht := act_time N x c d t h
  have hL := L0_le_Tpipe N
  rw [min_eq_right (by omega : N.L0 ≤ t + 1), if_pos (by omega)]
  unfold W0
  ring

include hdisp hord in
lemma whStock_prep (hx : x.Valid) (hs0S : c.s0 ≤ c.S0) (d : ℕ → DemandVec n) (t : ℕ)
    (h : ¬ act N x c d t) :
    0 ≤ Policy.whStock N x (conPolicy N x c).toPolicy () d t
      ∧ Policy.whStock N x (conPolicy N x c).toPolicy () d t ≤ W0 N x := by
  rw [whStock_eq N x c θ hdisp hord d t]
  have hV : V N x c d t = 0 := Finset.sum_eq_zero fun r hr => q0_zero N x c d r
    (fun h' => h (act_mono' N x c d (by simp at hr; omega) h'))
  have hsh : ∑ r ∈ Finset.range (t + 1), ∑ i, sh N x c θ d r i t = 0 :=
    Finset.sum_eq_zero fun r hr => Finset.sum_eq_zero fun i _ => sh_zero N x c θ d r i t
      (fun h' => h (act_mono' N x c d (by simp at hr; omega) h'))
  rw [hV, hsh]
  obtain ⟨hW, hsup, -⟩ := hx
  have hpart : ∑ s ∈ Finset.range (min (t + 1) N.L0), x.supPipe s
      ≤ ∑ s ∈ Finset.range N.L0, x.supPipe s :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (min_le_right _ _))
      fun s _ _ => hsup s
  have hpart0 : 0 ≤ ∑ s ∈ Finset.range (min (t + 1) N.L0), x.supPipe s :=
    Finset.sum_nonneg fun s _ => hsup s
  unfold W0
  split_ifs with h1
  · have hL := L0_le_Tpipe N
    rw [min_eq_right (by omega : N.L0 ≤ t + 1)]
    constructor <;> linarith [Finset.sum_nonneg fun s (_ : s ∈ Finset.range N.L0) => hsup s]
  · constructor <;> linarith

include hdisp in
lemma rP_run (d : ℕ → DemandVec n) (t : ℕ) (h : act N x c d t) (i : Fin n) :
    rP N x c d t i = IP N x c d t i + ∑ r ∈ Finset.range (t + 1), sh N x c θ d r i t := by
  unfold rP
  rw [cum_disp N x c θ hdisp d i t]
  have ht := act_time N x c d t h
  unfold IP W0
  by_cases hi : i = c.sendTo
  · rw [if_pos ⟨by omega, hi⟩, if_pos hi]; ring
  · rw [if_neg (fun h' => hi h'.2), if_neg hi]; ring

include hdisp in
lemma rP_prep (d : ℕ → DemandVec n) (t : ℕ) (h : ¬ act N x c d t) (i : Fin n) :
    rP N x c d t i = x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
      + (if N.Tpipe - 1 ≤ t ∧ i = c.sendTo then W0 N x else 0)
      - ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ) := by
  unfold rP
  rw [cum_disp N x c θ hdisp d i t]
  rw [Finset.sum_eq_zero fun r hr => sh_zero N x c θ d r i t
      (fun h' => h (act_mono' N x c d (by simp at hr; omega) h'))]
  ring

/-- A positive reserve forces a nonempty queue. -/
lemma reserve_pos (hsS : ∀ i, c.s i ≤ c.S i) (hs0S : c.s0 ≤ c.S0) (d : ℕ → DemandVec n) (t : ℕ)
    (hR : 0 < ∑ r ∈ Finset.range (t + 1), ∑ i, (A N x c d r i t - sh N x c θ d r i t)) :
    V N x c d t < Cq N x c d t := by
  have hR' : ∑ r ∈ Finset.range (t + 1), (0 : ℝ)
      < ∑ r ∈ Finset.range (t + 1), ∑ i, (A N x c d r i t - sh N x c θ d r i t) := by simpa using hR
  obtain ⟨r, hr, hr'⟩ := Finset.exists_lt_of_sum_lt hR'
  have hr'' : ∑ i ∈ (Finset.univ : Finset (Fin n)), (0 : ℝ)
      < ∑ i, (A N x c d r i t - sh N x c θ d r i t) := by simpa using hr'
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt hr''
  have hrt : r ≤ t := by simp at hr; omega
  obtain ⟨-, -, hfull⟩ := sh_props N x c θ hsS hs0S d r i t hrt
  have hAq : A N x c d r i t < q N x c d r i := lt_of_le_of_ne (A_le_q N x c hsS d r i t)
    (fun h => by have := hfull h; linarith)
  rw [A_eq] at hAq
  have hv : V N x c d t - ahead N x c d r i < q N x c d r i := by
    by_contra hc
    push Not at hc
    rw [min_eq_left hc, max_eq_right (q_nonneg N x c hsS d r i)] at hAq
    exact lt_irrefl _ hAq
  have h1 := ahead_add_le_Cq N x c hsS d r i
  have h2 : Cq N x c d r ≤ Cq N x c d t :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      fun r' _ _ => Finset.sum_nonneg fun j _ => q_nonneg N x c hsS d r' j
  linarith

/-- Only the partially allocated request holds a reserve. -/
lemma reserve_split (hsS : ∀ i, c.s i ≤ c.S i) (hs0S : c.s0 ≤ c.S0) (d : ℕ → DemandVec n)
    (t : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    max (∑ r ∈ Finset.range (t + 1), ∑ i, (A N x c d r i t - sh N x c θ d r i t) - z) 0
      ≤ ∑ r ∈ Finset.range (t + 1), ∑ i, max (A N x c d r i t - sh N x c θ d r i t - z) 0 := by
  have hnn : ∀ r ∈ Finset.range (t + 1), ∀ i, 0 ≤ A N x c d r i t - sh N x c θ d r i t :=
    fun r hr i => sub_nonneg.2 (sh_props N x c θ hsS hs0S d r i t (by simp at hr; omega)).2.1
  have hpart : ∀ r ∈ Finset.range (t + 1), ∀ i, A N x c d r i t - sh N x c θ d r i t ≠ 0 →
      0 < A N x c d r i t ∧ A N x c d r i t < q N x c d r i := by
    intro r hr i hne
    obtain ⟨h1, h2, h3⟩ := sh_props N x c θ hsS hs0S d r i t (by simp at hr; omega)
    have hpos : 0 < A N x c d r i t - sh N x c θ d r i t := lt_of_le_of_ne (hnn r hr i) (Ne.symm hne)
    refine ⟨by linarith, lt_of_le_of_ne (A_le_q N x c hsS d r i t) fun h => ?_⟩
    have := h3 h; linarith
  have hRHS : 0 ≤ ∑ r ∈ Finset.range (t + 1), ∑ i, max (A N x c d r i t - sh N x c θ d r i t - z) 0 :=
    Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun i _ => le_max_right _ _
  by_cases hex : ∃ r ∈ Finset.range (t + 1), ∃ i, A N x c d r i t - sh N x c θ d r i t ≠ 0
  · obtain ⟨r0, hr0, i0, hne⟩ := hex
    have huniq : ∀ r ∈ Finset.range (t + 1), ∀ i, A N x c d r i t - sh N x c θ d r i t ≠ 0 →
        r = r0 ∧ i = i0 := fun r hr i h =>
      partial_unique N x c hsS d t r r0 i i0 (hpart r hr i h) (hpart r0 hr0 i0 hne)
    have hR : ∑ r ∈ Finset.range (t + 1), ∑ i, (A N x c d r i t - sh N x c θ d r i t)
        = A N x c d r0 i0 t - sh N x c θ d r0 i0 t := by
      rw [Finset.sum_eq_single_of_mem r0 hr0 fun r hr hrr => Finset.sum_eq_zero fun i _ =>
        by_contra fun h => hrr (huniq r hr i h).1]
      rw [Finset.sum_eq_single_of_mem i0 (Finset.mem_univ _) fun i _ hii =>
        by_contra fun h => hii (huniq r0 hr0 i h).2]
    rw [hR]
    calc max (A N x c d r0 i0 t - sh N x c θ d r0 i0 t - z) 0
        ≤ ∑ i, max (A N x c d r0 i t - sh N x c θ d r0 i t - z) 0 :=
          Finset.single_le_sum (f := fun i => max (A N x c d r0 i t - sh N x c θ d r0 i t - z) 0)
            (fun i _ => le_max_right _ _) (Finset.mem_univ i0)
      _ ≤ _ := Finset.single_le_sum (f := fun r => ∑ i, max (A N x c d r i t - sh N x c θ d r i t - z) 0)
            (fun r _ => Finset.sum_nonneg fun i _ => le_max_right _ _) hr0
  · push Not at hex
    rw [Finset.sum_eq_zero fun r hr => Finset.sum_eq_zero fun i _ => hex r hr i]
    rw [max_eq_right (by linarith)]
    exact hRHS

include hdisp hord in
/-- The pathwise cost bound in a running period. -/
lemma path_run (hN : N.Standing) (hsS : ∀ i, c.s i ≤ c.S i) (hs0S : c.s0 ≤ c.S0)
    (d : ℕ → DemandVec n) (t : ℕ) (h : act N x c d t) :
    N.h * Policy.whStock N x (conPolicy N x c).toPolicy () d t
      + ∑ i, cH N i (rP N x c d t i - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ))
    ≤ whLoss N.h N.p (V N x c d t - Cq N x c d t - X N x c d t)
      + ∑ i, (cH N i (Ph N x c d t i - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ))
          + N.h * (c.S i - Ph N x c d t i))
      + (N.h + N.p) * ∑ r ∈ Finset.range (t + 1), ∑ i,
          max (A N x c d r i t - sh N x c θ d r i t - X N x c d t) 0 := by
  have hh := hN.h_pos.le
  have hp := hN.p_pos.le
  set R := ∑ r ∈ Finset.range (t + 1), ∑ i, (A N x c d r i t - sh N x c θ d r i t) with hRdef
  set Vt := V N x c d t with hVt
  set Ct := Cq N x c d t with hCt
  set Xt := X N x c d t with hXt
  have hV0 : 0 ≤ Vt := V_nonneg N x c hs0S d t
  have hC0 : 0 ≤ Ct := Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun j _ =>
    q_nonneg N x c hsS d r j
  have hX0 : 0 ≤ Xt := X_nonneg N x c hsS d t
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun r hr => Finset.sum_nonneg fun i _ =>
    sub_nonneg.2 (sh_props N x c θ hsS hs0S d r i t (by simp at hr; omega)).2.1
  have hsumA : ∑ r ∈ Finset.range (t + 1), ∑ i, A N x c d r i t = min Vt Ct := by
    rw [sum_A N x c hsS d t, max_eq_right (le_min hV0 hC0)]
  have hsumsh : ∑ r ∈ Finset.range (t + 1), ∑ i, sh N x c θ d r i t = min Vt Ct - R := by
    rw [← hsumA, hRdef]
    simp only [Finset.sum_sub_distrib]
    ring
  have hW : Policy.whStock N x (conPolicy N x c).toPolicy () d t = (Vt - min Vt Ct) + R := by
    rw [whStock_run N x c θ hdisp hord d t h, hsumsh]; ring
  have hrP : ∀ i, rP N x c d t i = Ph N x c d t i
      - ∑ r ∈ Finset.range (t + 1), (q N x c d r i - sh N x c θ d r i t) := fun i => by
    rw [rP_run N x c θ hdisp d t h i, Ph_run N x c d t h i, Finset.sum_sub_distrib]; ring
  have hqsh : ∀ i, 0 ≤ ∑ r ∈ Finset.range (t + 1), (q N x c d r i - sh N x c θ d r i t) :=
    fun i => Finset.sum_nonneg fun r hr => by
      have := (sh_props N x c θ hsS hs0S d r i t (by simp at hr; omega)).2.1
      have := A_le_q N x c hsS d r i t
      linarith
  have hcH : ∀ i, cH N i (rP N x c d t i
        - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ))
      ≤ cH N i (Ph N x c d t i - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ))
        + N.p * ∑ r ∈ Finset.range (t + 1), (q N x c d r i - sh N x c θ d r i t) := fun i => by
    have := cH_slope N hN i (rP N x c d t i
        - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ))
      (Ph N x c d t i - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ))
      (by rw [hrP i]; linarith [hqsh i])
    rw [hrP i] at this ⊢
    convert this using 2
    ring
  have hSig : ∑ i, ∑ r ∈ Finset.range (t + 1), (q N x c d r i - sh N x c θ d r i t)
      = (Ct - min Vt Ct) + R := by
    simp only [Finset.sum_sub_distrib]
    rw [Finset.sum_comm (s := Finset.univ), Finset.sum_comm (s := Finset.univ)
      (f := fun i r => sh N x c θ d r i t), hsumsh]
    unfold Cq at hCt
    rw [← hCt]
    ring
  have hloss : N.h * (Vt - min Vt Ct) + N.p * (Ct - min Vt Ct) = whLoss N.h N.p (Vt - Ct) := by
    unfold whLoss
    rcases le_total Vt Ct with hle | hle
    · rw [min_eq_left hle, max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [min_eq_right hle, max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have hkey : whLoss N.h N.p (Vt - Ct) + (N.h + N.p) * R
      ≤ whLoss N.h N.p (Vt - Ct - Xt) + N.h * Xt + (N.h + N.p) * max (R - Xt) 0 := by
    rcases eq_or_lt_of_le hR0 with hR | hR
    · rw [← hR]
      have := whLoss_add_le N.h N.p (Vt - Ct - Xt) Xt hh hp hX0
      rw [show Vt - Ct - Xt + Xt = Vt - Ct by ring] at this
      have : 0 ≤ (N.h + N.p) * max (0 - Xt) 0 := mul_nonneg (by linarith) (le_max_right _ _)
      linarith
    · have hVC : Vt < Ct := reserve_pos N x c θ hsS hs0S d t hR
      have e1 : whLoss N.h N.p (Vt - Ct) = N.p * (Ct - Vt) := by
        unfold whLoss; rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
      have e2 : whLoss N.h N.p (Vt - Ct - Xt) = N.p * (Ct - Vt + Xt) := by
        unfold whLoss; rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
      rw [e1, e2]
      have : R ≤ Xt + max (R - Xt) 0 := by linarith [le_max_left (R - Xt) 0]
      nlinarith
  have hsplit := reserve_split N x c θ hsS hs0S d t Xt hX0
  have hXsum : N.h * Xt = ∑ i, N.h * (c.S i - Ph N x c d t i) := by
    rw [hXt]; unfold X; rw [Finset.mul_sum]
  rw [hW]
  calc N.h * (Vt - min Vt Ct + R)
        + ∑ i, cH N i (rP N x c d t i - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ))
      ≤ N.h * (Vt - min Vt Ct + R)
        + ∑ i, (cH N i (Ph N x c d t i - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ))
          + N.p * ∑ r ∈ Finset.range (t + 1), (q N x c d r i - sh N x c θ d r i t)) := by
        gcongr with i; exact hcH i
    _ = (N.h * (Vt - min Vt Ct) + N.p * (Ct - min Vt Ct)) + (N.h + N.p) * R
        + ∑ i, cH N i (Ph N x c d t i - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hSig]; ring
    _ ≤ whLoss N.h N.p (Vt - Ct - Xt) + N.h * Xt + (N.h + N.p) * max (R - Xt) 0
        + ∑ i, cH N i (Ph N x c d t i - ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ)) := by
        rw [hloss]; linarith [hkey]
    _ ≤ _ := by
        rw [hXsum, Finset.sum_add_distrib]
        have := mul_le_mul_of_nonneg_left hsplit (by linarith : (0:ℝ) ≤ N.h + N.p)
        linarith

end ship2

end OWMR.Asm

end Part2

section Part3

/-! Assembly, part 3: supplier position identities, reserve reindexing and the credited bound. -/

open MeasureTheory
open scoped ENNReal NNReal


namespace OWMR.Asm

variable {n : ℕ} (N : Network n) (x : InitState n) (c : ConChoice n)

lemma CqX_run (d : ℕ → DemandVec n) (t : ℕ) (h : act N x c d t) :
    Cq N x c d t + X N x c d t = ∑ i, (c.S i - IP N x c d t i) := by
  rw [Cq_run N x c d t h]; unfold X; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- After `L₀` running periods the supplier loss sees the post-order position `L₀` periods earlier. -/
lemma E_shift (d : ℕ → DemandVec n) (t : ℕ) (ht : N.L0 ≤ t) (h : act N x c d (t - N.L0)) :
    V N x c d t - Cq N x c d t - X N x c d t
      = Ypost N x c d (t - N.L0)
        - ∑ j ∈ Finset.range N.L0, ((∑ i, d (t - N.L0 + j) i : ℝ≥0) : ℝ) := by
  have h' : act N x c d t := act_mono' N x c d (Nat.sub_le t N.L0) h
  have hV : V N x c d t = ∑ r ∈ Finset.range (t - N.L0 + 1), q0 N x c d r := by
    unfold V; rw [show t + 1 - N.L0 = t - N.L0 + 1 by omega]
  have hk := key_id N x c d (t - N.L0) h
  have h1 := CqX_run N x c d t h'
  have h2 := CqX_run N x c d (t - N.L0) h
  have hIP : ∀ i, IP N x c d (t - N.L0) i - IP N x c d t i
      = ∑ j ∈ Finset.range N.L0, ((d (t - N.L0 + j) i : ℝ≥0) : ℝ) := fun i => by
    unfold IP
    rw [show t = (t - N.L0) + N.L0 from (Nat.sub_add_cancel ht).symm, Finset.sum_range_add]
    simp only [Nat.add_sub_cancel]
    ring
  have hD : ∑ j ∈ Finset.range N.L0, ((∑ i, d (t - N.L0 + j) i : ℝ≥0) : ℝ)
      = ∑ i, (IP N x c d (t - N.L0) i - IP N x c d t i) := by
    simp_rw [hIP]
    rw [Finset.sum_comm]
    simp only [NNReal.coe_sum]
  rw [hV, hD]
  have e : ∑ i, (IP N x c d (t - N.L0) i - IP N x c d t i)
      = ∑ i, (c.S i - IP N x c d t i) - ∑ i, (c.S i - IP N x c d (t - N.L0) i) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  linarith

/-- In the first `L₀` running periods no order has arrived. -/
lemma E_trans (d : ℕ → DemandVec n) (t : ℕ) (h : act N x c d t)
    (h' : ¬ (N.L0 ≤ t ∧ act N x c d (t - N.L0))) :
    V N x c d t - Cq N x c d t - X N x c d t = ∑ i, (IP N x c d t i - c.S i) := by
  have hV : V N x c d t = 0 := by
    unfold V
    refine Finset.sum_eq_zero fun r hr => q0_zero N x c d r fun hr' => ?_
    simp only [Finset.mem_range] at hr
    by_cases hL : N.L0 ≤ t
    · exact h' ⟨hL, act_mono' N x c d (by omega) hr'⟩
    · have : r = 0 := by omega
      subst this
      exact not_act_zero N x c d hr'
  have h1 := CqX_run N x c d t h
  rw [hV]
  have : ∑ i, (IP N x c d t i - c.S i) = -∑ i, (c.S i - IP N x c d t i) := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]; linarith

lemma persp (a e z : ℝ) (ha : 0 < a) (he : 0 ≤ e) (hz : 0 ≤ z) :
    max (a + e - z) 0 ^ 2 / (a + e) ≤ e + max (a - z) 0 ^ 2 / a := by
  have hae : 0 < a + e := by linarith
  rcases le_or_gt (a + e) z with h1 | h1
  · rw [max_eq_right (by linarith)]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
    positivity
  · rw [max_eq_left (by linarith)]
    rcases le_or_gt a z with h2 | h2
    · rw [max_eq_right (by linarith)]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, add_zero]
      rw [div_le_iff₀ hae]
      nlinarith
    · rw [max_eq_left (by linarith), div_le_iff₀ hae]
      have : e + (a - z) ^ 2 / a = (e * a + (a - z) ^ 2) / a := by field_simp
      rw [this, div_mul_eq_mul_div, le_div_iff₀ ha]
      nlinarith [mul_nonneg he (sq_nonneg z)]

lemma mono_b (b b' z : ℝ) (hb : 0 < b) (hbb : b ≤ b') (hz : 0 ≤ z) :
    max (b - z) 0 ^ 2 / (2 * b) ≤ max (b' - z) 0 ^ 2 / (2 * b') := by
  have hb' : 0 < b' := by linarith
  rcases le_or_gt b z with h1 | h1
  · rw [max_eq_right (by linarith)]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
    positivity
  · rw [max_eq_left (by linarith), max_eq_left (by linarith),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.2 hbb) (sub_nonneg.2 (show z * z ≤ b * b' by nlinarith))]

/-- The credited reserve bound: trigger term plus width term. -/
lemma cred_alg (Q w dd z zi : ℝ) (hQ : 0 < Q) (hw : 0 < w) (hdd : 0 ≤ dd) (hQw : Q ≤ w + dd)
    (hz : zi ≤ z) (hzi : 0 ≤ zi) :
    max (3 * Q / 4 - z) 0 ^ 2 / (3 * Q / 2)
      ≤ 3 / 8 * dd + w * (max (1 - 4 * (zi / w) / 3) 0 ^ 2 / (8 / 3)) := by
  have hz0 : 0 ≤ z := le_trans hzi hz
  have h1 := mono_b (3 * Q / 4) (3 * (w + dd) / 4) z (by positivity) (by linarith) hz0
  have h2 := persp (3 * w / 4) (3 * dd / 4) z (by positivity) (by positivity) hz0
  have e1 : 3 * Q / 2 = 2 * (3 * Q / 4) := by ring
  have e2 : 3 * (w + dd) / 4 = 3 * w / 4 + 3 * dd / 4 := by ring
  rw [e1]
  refine le_trans h1 ?_
  rw [e2]
  have h3 : max (3 * w / 4 + 3 * dd / 4 - z) 0 ^ 2 / (2 * (3 * w / 4 + 3 * dd / 4))
      ≤ 3 / 8 * dd + max (3 * w / 4 - z) 0 ^ 2 / (3 * w / 2) := by
    have : max (3 * w / 4 + 3 * dd / 4 - z) 0 ^ 2 / (2 * (3 * w / 4 + 3 * dd / 4))
        = (max (3 * w / 4 + 3 * dd / 4 - z) 0 ^ 2 / (3 * w / 4 + 3 * dd / 4)) / 2 := by
      field_simp
    rw [this]
    have e3 : 3 / 8 * dd + max (3 * w / 4 - z) 0 ^ 2 / (3 * w / 2)
        = (3 * dd / 4 + max (3 * w / 4 - z) 0 ^ 2 / (3 * w / 4)) / 2 := by
      field_simp; ring
    rw [e3]
    exact div_le_div_of_nonneg_right h2 (by norm_num)
  refine le_trans h3 (add_le_add le_rfl ?_)
  have h4 : max (3 * w / 4 - z) 0 ≤ max (3 * w / 4 - zi) 0 := max_le_max (by linarith) le_rfl
  have h5 : max (3 * w / 4 - z) 0 ^ 2 ≤ max (3 * w / 4 - zi) 0 ^ 2 :=
    pow_le_pow_left₀ (le_max_right _ _) h4 2
  have e4 : w * (max (1 - 4 * (zi / w) / 3) 0 ^ 2 / (8 / 3))
      = max (3 * w / 4 - zi) 0 ^ 2 / (3 * w / 2) := by
    have : max (1 - 4 * (zi / w) / 3) 0 = max (3 * w / 4 - zi) 0 * (4 / (3 * w)) := by
      rw [max_mul_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 4 / (3 * w)), zero_mul]
      congr 1; field_simp
    rw [this]; field_simp; ring
  rw [e4]
  exact div_le_div_of_nonneg_right h5 (by positivity)

section ship3

variable (θ : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)

/-- Reserve terms vanish once a request is fully allocated. -/
lemma res_zero (hsS : ∀ i, c.s i ≤ c.S i) (hs0 : 0 ≤ c.s0) (hs0S : c.s0 ≤ c.S0)
    (d : ℕ → DemandVec n) (r : ℕ) (i : Fin n) (t : ℕ) (hrt : r + N.L0 ≤ t) :
    max (A N x c d r i t - sh N x c θ d r i t - X N x c d t) 0 = 0 := by
  have hX := X_nonneg N x c hsS d t
  by_cases hr : act N x c d r
  · have hA := A_full N x c hsS hs0 hs0S d r i t hr hrt
    have hs := (sh_props N x c θ hsS hs0S d r i t (by omega)).2.2 hA
    rw [hA, hs]; simp [hX]
  · rw [A_zero N x c d r i t hr, sh_zero N x c θ d r i t hr]; simp [hX]

/-- Reindexing the reserve by request and age. -/
lemma res_reindex (hsS : ∀ i, c.s i ≤ c.S i) (hs0 : 0 ≤ c.s0) (hs0S : c.s0 ≤ c.S0)
    (d : ℕ → DemandVec n) (T : ℕ) :
    ∑ t ∈ Finset.range T, ∑ r ∈ Finset.range (t + 1), ∑ i,
        max (A N x c d r i t - sh N x c θ d r i t - X N x c d t) 0
      ≤ ∑ r ∈ Finset.range T, ∑ i, ∑ k ∈ Finset.range (N.L0 + 1),
        max (A N x c d r i (r + k) - sh N x c θ d r i (r + k) - X N x c d (r + k)) 0 := by
  set f : ℕ → ℕ → ℝ := fun r t => ∑ i, max (A N x c d r i t - sh N x c θ d r i t - X N x c d t) 0
    with hf
  have hf0 : ∀ r t, 0 ≤ f r t := fun r t => Finset.sum_nonneg fun i _ => le_max_right _ _
  have hfz : ∀ r t, r + N.L0 ≤ t → f r t = 0 := fun r t h =>
    Finset.sum_eq_zero fun i _ => res_zero N x c θ hsS hs0 hs0S d r i t h
  change ∑ t ∈ Finset.range T, ∑ r ∈ Finset.range (t + 1), f r t
    ≤ ∑ r ∈ Finset.range T, ∑ i, ∑ k ∈ Finset.range (N.L0 + 1),
      max (A N x c d r i (r + k) - sh N x c θ d r i (r + k) - X N x c d (r + k)) 0
  have e : ∀ r, ∑ i, ∑ k ∈ Finset.range (N.L0 + 1),
      max (A N x c d r i (r + k) - sh N x c θ d r i (r + k) - X N x c d (r + k)) 0
      = ∑ k ∈ Finset.range (N.L0 + 1), f r (r + k) := fun r => Finset.sum_comm
  simp_rw [e]
  -- swap the order of summation
  have hsw : ∑ t ∈ Finset.range T, ∑ r ∈ Finset.range (t + 1), f r t
      = ∑ r ∈ Finset.range T, ∑ t ∈ Finset.Ico r T, f r t := by
    refine Finset.sum_comm' fun t r => ?_
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hsw]
  refine Finset.sum_le_sum fun r hr => ?_
  calc ∑ t ∈ Finset.Ico r T, f r t ≤ ∑ t ∈ Finset.Ico r (max T (r + (N.L0 + 1))), f r t :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl (le_max_left _ _))
          fun t _ _ => hf0 r t
    _ = ∑ t ∈ Finset.Ico r (r + (N.L0 + 1)), f r t := by
        rw [← Finset.sum_Ico_consecutive _ (show r ≤ r + (N.L0 + 1) by omega)
          (le_max_right T (r + (N.L0 + 1)))]
        rw [Finset.sum_eq_zero (s := Finset.Ico (r + (N.L0 + 1)) (max T (r + (N.L0 + 1))))
          fun t ht => hfz r t (by simp only [Finset.mem_Ico] at ht; omega), add_zero]
    _ = ∑ k ∈ Finset.range (N.L0 + 1), f r (r + k) := Finset.sum_Ico_eq_sum_range _ _ _ |>.trans
        (by simp)

/-- A crossing of request `(s, i)` at age `k`. -/
abbrev cross (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) (k : ℕ) : Prop :=
  crossesThreshold (q N x c d s i) (θ d s i) (if k = 0 then 0 else A N x c d s i (s + (k - 1)))
    (A N x c d s i (s + k))

variable (hdisp : ∀ d t i, (conPolicy N x c).dispatch t d i = if act N x c d t then
        ∑ s ∈ Finset.range (t + 1),
          ((if c.batch i then shippedPath (q N x c d s i) (θ d s i)
                (fun k => A N x c d s i (s + k)) (t - s)
              else A N x c d s i t)
            - if s < t then (if c.batch i then
                shippedPath (q N x c d s i) (θ d s i) (fun k => A N x c d s i (s + k)) (t - 1 - s)
              else A N x c d s i (t - 1)) else 0)
        else if t = N.Tpipe - 1 ∧ i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
        else 0)

include hdisp in
lemma disp_cross (d : ℕ → DemandVec n) (t : ℕ) (i : Fin n) (hb : c.batch i = true)
    (h : act N x c d t) (hpos : 0 < (conPolicy N x c).dispatch t d i) :
    ∃ s ∈ Finset.range (t + 1), cross N x c θ d s i (t - s) := by
  rw [disp_run N x c θ hdisp d t i h] at hpos
  obtain ⟨s, hs, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  refine ⟨s, hs, ?_⟩
  have hst : s ≤ t := by simp at hs; omega
  unfold sh at hne
  rw [if_pos hb] at hne
  by_contra hc
  unfold cross at hc
  rcases eq_or_lt_of_le hst with heq | hlt
  · subst heq
    rw [if_neg (lt_irrefl s), Nat.sub_self] at hne
    simp only [shippedPath] at hne
    rw [if_neg (by simpa using hc)] at hne
    exact hne (by ring)
  · rw [if_pos hlt, if_pos hb] at hne
    obtain ⟨k, hk⟩ : ∃ k, t - s = k + 1 := ⟨t - s - 1, by omega⟩
    have hk' : t - 1 - s = k := by omega
    rw [hk, hk'] at hne
    rw [hk] at hc
    simp only [shippedPath] at hne
    rw [if_neg (by simpa [show s + (k + 1 - 1) = s + k by omega] using hc)] at hne
    exact hne (by ring)

lemma cross_zero (hsS : ∀ i, c.s i ≤ c.S i) (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) (k : ℕ)
    (hq : q N x c d s i = 0) : ¬ cross N x c θ d s i k := by
  have hA : ∀ k', A N x c d s i k' = 0 := fun k' =>
    le_antisymm (by rw [← hq]; exact A_le_q N x c hsS d s i k') (A_nonneg N x c d s i k')
  unfold cross
  rw [hA, hq]
  simp only [crossesThreshold, zero_div, zero_mul, mul_zero, zero_add, lt_irrefl, false_and,
    and_false, or_self, not_false_eq_true]
  split_ifs <;> simp [hA]

include hdisp in
/-- Dispatch periods of a batch retailer are bounded by charged shipments. -/
lemma setup_count (hsS : ∀ i, c.s i ≤ c.S i) (hs0S : c.s0 ≤ c.S0)
    (hθ : ∀ d s i, 0 < θ d s i ∧ θ d s i < 1) (d : ℕ → DemandVec n) (i : Fin n)
    (hb : c.batch i = true) (T : ℕ) :
    ∑ t ∈ Finset.range T, (if act N x c d t ∧ 0 < (conPolicy N x c).dispatch t d i then (1 : ℝ)
      else 0)
      ≤ ∑ s ∈ Finset.range T,
          (if 0 < q N x c d s i then 1 + (if θ d s i < 1 / 3 then 2 else 1) else 0) := by
  classical
  have step1 : ∀ t, (if act N x c d t ∧ 0 < (conPolicy N x c).dispatch t d i then (1 : ℝ) else 0)
      ≤ ∑ s ∈ Finset.range (t + 1), (if cross N x c θ d s i (t - s) then (1 : ℝ) else 0) := by
    intro t
    split_ifs with h
    · obtain ⟨s, hs, hc⟩ := disp_cross N x c θ hdisp d t i hb h.1 h.2
      calc (1 : ℝ) = if cross N x c θ d s i (t - s) then 1 else 0 := by rw [if_pos hc]
        _ ≤ _ := Finset.single_le_sum (f := fun s => if cross N x c θ d s i (t - s) then (1 : ℝ)
            else 0) (fun s _ => by split_ifs <;> norm_num) hs
    · exact Finset.sum_nonneg fun s _ => by split_ifs <;> norm_num
  refine le_trans (Finset.sum_le_sum fun t _ => step1 t) ?_
  have hsw : ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range (t + 1),
        (if cross N x c θ d s i (t - s) then (1 : ℝ) else 0)
      = ∑ s ∈ Finset.range T, ∑ t ∈ Finset.Ico s T,
        (if cross N x c θ d s i (t - s) then (1 : ℝ) else 0) := by
    refine Finset.sum_comm' fun t s => ?_
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hsw]
  refine Finset.sum_le_sum fun s hs => ?_
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  by_cases hq : 0 < q N x c d s i
  · rw [if_pos hq]
    obtain ⟨-, -, c3, -, -⟩ := arb_credited_reserve (q N x c d s i)
      (fun k => A N x c d s i (s + k)) hq (A_nonneg N x c d s i _)
      (fun k k' hk => A_mono N x c hs0S d s i (by omega)) (fun k => A_le_q N x c hsS d s i _)
    exact c3 (θ d s i) (T - s) (hθ d s i).1
  · rw [if_neg hq]
    have hq0 : q N x c d s i = 0 := le_antisymm (not_lt.1 hq) (q_nonneg N x c hsS d s i)
    exact le_of_eq (Finset.sum_eq_zero fun k _ => if_neg (cross_zero N x c θ hsS d s i k hq0))

/-- Batch retailers. -/
def bset : Finset (Fin n) := Finset.univ.filter fun i => c.batch i = true

/-- Batch demand in a period. -/
def DP (d : ℕ → DemandVec n) (l : ℕ) : ℝ≥0 := ∑ i ∈ bset c, d l i

/-- Largest batch demand in the `L₀` periods before `t` (the first `L₀` periods if `t < L₀`). -/
def Vmax (d : ℕ → DemandVec n) (t : ℕ) : ℝ :=
  ((Finset.univ.sup fun j : Fin N.L0 => DP c d (t - N.L0 + j) : ℝ≥0) : ℝ)

/-- The shortage event used for the trigger and width terms. -/
def Bp (d : ℕ → DemandVec n) (t : ℕ) : Prop :=
  if N.L0 ≤ t ∧ act N x c d (t - N.L0) then
    Ypost N x c d (t - N.L0) < ∑ j ∈ Finset.range N.L0, ((∑ i, d (t - N.L0 + j) i : ℝ≥0) : ℝ)
  else act N x c d t

instance BpDec (d : ℕ → DemandVec n) (t : ℕ) : Decidable (Bp N x c d t) := Classical.dec _

/-- The normalized width loss `ψ`. -/
def psi (u : ℝ) : ℝ := max (1 - 4 * u / 3) 0 ^ 2 / (8 / 3)

lemma psi_nonneg (u : ℝ) : 0 ≤ psi u := by unfold psi; positivity

lemma psi_le (u : ℝ) (hu : 0 ≤ u) : psi u ≤ 3 / 8 := by
  unfold psi
  have h1 : max (1 - 4 * u / 3) 0 ≤ 1 := max_le (by linarith) zero_le_one
  have h2 : max (1 - 4 * u / 3) 0 ^ 2 ≤ 1 := by
    have := le_max_right (1 - 4 * u / 3) 0; nlinarith
  rw [div_le_iff₀ (by norm_num)]; linarith

/-- The per-period trigger and width bound. -/
def pp (d : ℕ → DemandVec n) (t : ℕ) : ℝ :=
  (N.h + N.p) * (3 / 8 * Vmax N c d t * (if Bp N x c d t then 1 else 0)
    + ∑ i ∈ bset c, min (3 / 8 * (c.S i - c.s i) * (if Bp N x c d t then 1 else 0))
        ((if act N x c d t then 1 else 0) * ((c.S i - c.s i) * psi ((c.S i - Ph N x c d t i) / (c.S i - c.s i)))))

lemma pp_nonneg (hN : N.Standing) (hw : ∀ i, c.batch i = true → c.s i < c.S i)
    (d : ℕ → DemandVec n) (t : ℕ) : 0 ≤ pp N x c d t := by
  unfold pp
  have hh := hN.h_pos; have hp := hN.p_pos
  refine mul_nonneg (by linarith) (add_nonneg ?_ (Finset.sum_nonneg fun i hi => ?_))
  · have : 0 ≤ Vmax N c d t := NNReal.coe_nonneg _
    split_ifs <;> positivity
  · have hwi : 0 < c.S i - c.s i := sub_pos.2 (hw i (by simpa [bset] using hi))
    have := psi_nonneg ((c.S i - Ph N x c d t i) / (c.S i - c.s i))
    refine le_min ?_ ?_ <;> split_ifs <;> positivity

/-- The credited bound of an ordinary request in one period. -/
def crA (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) (t : ℕ) : ℝ :=
  max (3 * q N x c d s i / 4 - X N x c d t) 0 ^ 2 / (3 * q N x c d s i / 2)

/-- Ordinary requests of batch retailers. -/
def ord (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) : Prop :=
  0 < s ∧ act N x c d (s - 1) ∧ 0 < q N x c d s i ∧ c.batch i = true

instance ordDec (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) : Decidable (ord N x c d s i) :=
  Classical.dec _

lemma cr_le_pp (hN : N.Standing) (hsS : ∀ i, c.s i ≤ c.S i) (hs0 : 0 ≤ c.s0) (hs0S : c.s0 ≤ c.S0)
    (hw : ∀ i, c.batch i = true → c.s i < c.S i) (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n)
    (t : ℕ) (ho : ord N x c d s i) (hst : s ≤ t)
    (hpart : 0 < A N x c d s i t ∧ A N x c d s i t < q N x c d s i) :
    (N.h + N.p) * crA N x c d s i t ≤ pp N x c d t := by
  obtain ⟨hs1, has, hq, hb⟩ := ho
  have hh := hN.h_pos; have hp := hN.p_pos
  have hact_s : act N x c d s := by
    have := act_mono N x c d (s - 1) has; rwa [Nat.sub_add_cancel hs1] at this
  have hact_t : act N x c d t := act_mono' N x c d hst hact_s
  -- partial allocation happens before the request is complete
  have hkL : t < s + N.L0 := by
    by_contra hc
    have := A_full N x c hsS hs0 hs0S d s i t hact_s (by omega)
    linarith [hpart.2]
  have hwi : 0 < c.S i - c.s i := sub_pos.2 (hw i hb)
  -- the request size
  set dd : ℝ := ((d (s - 1) i : ℝ≥0) : ℝ) with hdd
  have hQ : q N x c d s i ≤ (c.S i - c.s i) + dd := by
    have e := q_ord N x c d (s - 1) has i
    rw [Nat.sub_add_cancel hs1] at e
    rw [e] at hq ⊢
    split_ifs at hq ⊢ with h1
    · have := (Ph_bounds N x c hsS d (s - 1) i).1
      linarith
    · exact absurd hq (lt_irrefl 0)
  have hzi : c.S i - Ph N x c d t i ≤ X N x c d t := by
    unfold X
    exact Finset.single_le_sum (f := fun j => c.S j - Ph N x c d t j)
      (fun j _ => sub_nonneg.2 (Ph_bounds N x c hsS d t j).2) (Finset.mem_univ i)
  have hzi0 : 0 ≤ c.S i - Ph N x c d t i := sub_nonneg.2 (Ph_bounds N x c hsS d t i).2
  have hcr := cred_alg (q N x c d s i) (c.S i - c.s i) dd (X N x c d t) (c.S i - Ph N x c d t i)
    hq hwi (NNReal.coe_nonneg _) hQ hzi hzi0
  -- the trigger lies in the window
  have hdd_le : dd ≤ Vmax N c d t := by
    have hj : s - 1 - (t - N.L0) < N.L0 := by omega
    have e : t - N.L0 + (s - 1 - (t - N.L0)) = s - 1 := by omega
    have h1 : d (s - 1) i ≤ DP c d (s - 1) := by
      unfold DP
      exact Finset.single_le_sum (f := fun j => d (s - 1) j) (fun j _ => by positivity)
        (by simp [bset, hb])
    have h2 : DP c d (s - 1) ≤ Finset.univ.sup fun j : Fin N.L0 => DP c d (t - N.L0 + j) := by
      have := Finset.le_sup (f := fun j : Fin N.L0 => DP c d (t - N.L0 + j))
        (Finset.mem_univ ⟨s - 1 - (t - N.L0), hj⟩)
      simp only at this
      rwa [e] at this
    unfold Vmax
    exact_mod_cast le_trans h1 h2
  -- the shortage event holds
  have hBp : Bp N x c d t := by
    have hVC : V N x c d t < Cq N x c d t := by
      have h1 := hpart.2
      rw [A_eq] at h1
      have hv : V N x c d t - ahead N x c d s i < q N x c d s i := by
        by_contra hc
        push Not at hc
        rw [min_eq_left hc, max_eq_right (q_nonneg N x c hsS d s i)] at h1
        exact lt_irrefl _ h1
      have h2 := ahead_add_le_Cq N x c hsS d s i
      have h3 : Cq N x c d s ≤ Cq N x c d t :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
          fun r' _ _ => Finset.sum_nonneg fun j _ => q_nonneg N x c hsS d r' j
      linarith
    unfold Bp
    split_ifs with hc
    · have := E_shift N x c d t hc.1 hc.2
      have hX := X_nonneg N x c hsS d t
      linarith
    · exact hact_t
  have hψ := psi_le ((c.S i - Ph N x c d t i) / (c.S i - c.s i)) (div_nonneg hzi0 hwi.le)
  have hψ0 := psi_nonneg ((c.S i - Ph N x c d t i) / (c.S i - c.s i))
  unfold pp
  rw [if_pos hBp, if_pos hact_t]
  have hterm : (c.S i - c.s i) * psi ((c.S i - Ph N x c d t i) / (c.S i - c.s i))
      ≤ min (3 / 8 * (c.S i - c.s i) * 1)
          (1 * ((c.S i - c.s i) * psi ((c.S i - Ph N x c d t i) / (c.S i - c.s i)))) := by
    rw [mul_one, one_mul]
    exact le_min (by nlinarith) le_rfl
  have hsum : min (3 / 8 * (c.S i - c.s i) * 1)
      (1 * ((c.S i - c.s i) * psi ((c.S i - Ph N x c d t i) / (c.S i - c.s i))))
      ≤ ∑ j ∈ bset c, min (3 / 8 * (c.S j - c.s j) * (if Bp N x c d t then 1 else 0))
        ((if act N x c d t then 1 else 0) * ((c.S j - c.s j)
          * psi ((c.S j - Ph N x c d t j) / (c.S j - c.s j)))) := by
    rw [if_pos hBp, if_pos hact_t]
    refine Finset.single_le_sum (f := fun j => min (3 / 8 * (c.S j - c.s j) * 1)
      (1 * ((c.S j - c.s j) * psi ((c.S j - Ph N x c d t j) / (c.S j - c.s j))))) (fun j hj => ?_)
      (by simp [bset, hb])
    have hwj : 0 < c.S j - c.s j := sub_pos.2 (hw j (by simpa [bset] using hj))
    have := psi_nonneg ((c.S j - Ph N x c d t j) / (c.S j - c.s j))
    exact le_min (by positivity) (by positivity)
  rw [if_pos hBp, if_pos hact_t] at hsum
  have : 3 / 8 * dd ≤ 3 / 8 * Vmax N c d t := by linarith
  have hfin : crA N x c d s i t ≤ 3 / 8 * Vmax N c d t * 1
      + ∑ j ∈ bset c, min (3 / 8 * (c.S j - c.s j) * 1)
        (1 * ((c.S j - c.s j) * psi ((c.S j - Ph N x c d t j) / (c.S j - c.s j)))) := by
    have hcr' : crA N x c d s i t ≤ 3 / 8 * dd
        + (c.S i - c.s i) * psi ((c.S i - Ph N x c d t i) / (c.S i - c.s i)) := by
      unfold crA psi; exact hcr
    linarith [hcr', hterm, hsum]
  exact mul_le_mul_of_nonneg_left hfin (by linarith)

/-- Summing the credited bounds of ordinary requests by period. -/
lemma sum_cr_le (hN : N.Standing) (hsS : ∀ i, c.s i ≤ c.S i) (hs0 : 0 ≤ c.s0) (hs0S : c.s0 ≤ c.S0)
    (hw : ∀ i, c.batch i = true → c.s i < c.S i) (d : ℕ → DemandVec n) (T : ℕ) :
    ∑ s ∈ Finset.range T, ∑ i, (if ord N x c d s i then ∑ k ∈ Finset.range (N.L0 + 1),
        (if 0 < A N x c d s i (s + k) ∧ A N x c d s i (s + k) < q N x c d s i then
          (N.h + N.p) * crA N x c d s i (s + k) else 0) else 0)
      ≤ ∑ t ∈ Finset.range (T + N.L0), pp N x c d t := by
  set F : ℕ → Fin n → ℕ → ℝ := fun s i t =>
    if ord N x c d s i ∧ (0 < A N x c d s i t ∧ A N x c d s i t < q N x c d s i) then
      (N.h + N.p) * crA N x c d s i t else 0 with hF
  have e1 : ∀ s i, (if ord N x c d s i then ∑ k ∈ Finset.range (N.L0 + 1),
        (if 0 < A N x c d s i (s + k) ∧ A N x c d s i (s + k) < q N x c d s i then
          (N.h + N.p) * crA N x c d s i (s + k) else 0) else 0)
      = ∑ t ∈ Finset.Ico s (s + (N.L0 + 1)), F s i t := by
    intro s i
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    by_cases ho : ord N x c d s i
    · rw [if_pos ho]
      exact Finset.sum_congr rfl fun k _ => by
        simp only [hF]
        by_cases hpa : 0 < A N x c d s i (s + k) ∧ A N x c d s i (s + k) < q N x c d s i
        · rw [if_pos hpa, if_pos ⟨ho, hpa⟩]
        · rw [if_neg hpa, if_neg (fun h => hpa h.2)]
    · rw [if_neg ho]
      exact (Finset.sum_eq_zero fun k _ => by simp only [hF]; rw [if_neg (fun h => ho h.1)]).symm
  simp_rw [e1]
  have e2 : ∑ s ∈ Finset.range T, ∑ i, ∑ t ∈ Finset.Ico s (s + (N.L0 + 1)), F s i t
      = ∑ s ∈ Finset.range T, ∑ t ∈ Finset.Ico s (s + (N.L0 + 1)), ∑ i, F s i t :=
    Finset.sum_congr rfl fun s _ => Finset.sum_comm
  rw [e2]
  have e3 : ∑ s ∈ Finset.range T, ∑ t ∈ Finset.Ico s (s + (N.L0 + 1)), ∑ i, F s i t
      = ∑ t ∈ Finset.range (T + N.L0),
          ∑ s ∈ (Finset.range T).filter (fun s => s ≤ t ∧ t < s + (N.L0 + 1)), ∑ i, F s i t := by
    refine Finset.sum_comm' fun s t => ?_
    simp only [Finset.mem_range, Finset.mem_Ico, Finset.mem_filter]
    omega
  rw [e3]
  refine Finset.sum_le_sum fun t _ => ?_
  have hF0 : ∀ s i, 0 ≤ F s i t := fun s i => by
    simp only [hF]
    split_ifs
    · unfold crA
      have := hN.h_pos; have := hN.p_pos
      have : 0 ≤ q N x c d s i := q_nonneg N x c hsS d s i
      positivity
    · exact le_rfl
  by_cases hex : ∃ s ∈ (Finset.range T).filter (fun s => s ≤ t ∧ t < s + (N.L0 + 1)),
      ∃ i, F s i t ≠ 0
  · obtain ⟨s0, hs0m, i0, hne⟩ := hex
    have hpos : ∀ s i, F s i t ≠ 0 → ord N x c d s i ∧
        (0 < A N x c d s i t ∧ A N x c d s i t < q N x c d s i) := fun s i h => by
      simp only [hF] at h
      by_contra hc
      exact h (if_neg hc)
    have huniq : ∀ s i, F s i t ≠ 0 → s = s0 ∧ i = i0 := fun s i h =>
      partial_unique N x c hsS d t s s0 i i0 (hpos s i h).2 (hpos s0 i0 hne).2
    have hsum : ∑ s ∈ (Finset.range T).filter (fun s => s ≤ t ∧ t < s + (N.L0 + 1)),
        ∑ i, F s i t = F s0 i0 t := by
      rw [Finset.sum_eq_single_of_mem s0 hs0m fun s _ hss => Finset.sum_eq_zero fun i _ =>
        by_contra fun h => hss (huniq s i h).1]
      rw [Finset.sum_eq_single_of_mem i0 (Finset.mem_univ _) fun i _ hii =>
        by_contra fun h => hii (huniq s0 i h).2]
    rw [hsum]
    obtain ⟨ho, hpa⟩ := hpos s0 i0 hne
    simp only [hF]
    rw [if_pos ⟨ho, hpa⟩]
    have hst : s0 ≤ t := (Finset.mem_filter.1 hs0m).2.1
    exact cr_le_pp N x c hN hsS hs0 hs0S hw d s0 i0 t ho hst hpa
  · push Not at hex
    rw [Finset.sum_eq_zero fun s hs => Finset.sum_eq_zero fun i _ => hex s hs i]
    exact pp_nonneg N x c hN hw d t

end ship3

end OWMR.Asm

end Part3

section Part4

/-! Assembly, part 4: the pathwise decomposition of the total cost over a horizon. -/

open MeasureTheory
open scoped ENNReal NNReal


namespace OWMR.Asm

variable {n : ℕ} (N : Network n) (x : InitState n) (c : ConChoice n)

/-- Charged shipments of a batch request with offset `ϑ`. -/
def Ncnt (θ' : ℝ) : ℝ := 1 + if θ' < 1 / 3 then 2 else 1

/-- The credited full-lifetime proxy of the ordinary request `(s, i)` along the path `d`. -/
def Zexp (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) (θ' : ℝ) : ℝ :=
  N.K i * Ncnt θ' + (N.h + N.p) * ∑ k ∈ Finset.range (N.L0 + 1),
    max (A N x c d s i (s + k) - shippedPath (q N x c d s i) θ' (fun k => A N x c d s i (s + k)) k
      - X N x c d (s + k)) 0

/-- The start period. -/
def start (d : ℕ → DemandVec n) (t : ℕ) : Prop := act N x c d t ∧ ¬ act N x c d (t - 1)

instance startDec (d : ℕ → DemandVec n) (t : ℕ) : Decidable (start N x c d t) := Classical.dec _

/-- Positions charged for the physical retailer costs. -/
def Pos (d : ℕ → DemandVec n) (t : ℕ) (i : Fin n) : ℝ :=
  if act N x c d t then Ph N x c d t i else rP N x c d t i

/-- Lead-time demand of retailer `i` from period `t`. -/
def Dblk (d : ℕ → DemandVec n) (t : ℕ) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.range (N.L i + 1), ((d (t + j) i : ℝ≥0) : ℝ)

lemma Ncnt_le (θ' : ℝ) : Ncnt θ' ≤ 3 := by unfold Ncnt; split_ifs <;> norm_num

lemma Ncnt_nonneg (θ' : ℝ) : 0 ≤ Ncnt θ' := by unfold Ncnt; split_ifs <;> norm_num

section path4

variable (θ : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)
  (hdisp : ∀ d t i, (conPolicy N x c).dispatch t d i = if act N x c d t then
        ∑ s ∈ Finset.range (t + 1),
          ((if c.batch i then shippedPath (q N x c d s i) (θ d s i)
                (fun k => A N x c d s i (s + k)) (t - s)
              else A N x c d s i t)
            - if s < t then (if c.batch i then
                shippedPath (q N x c d s i) (θ d s i) (fun k => A N x c d s i (s + k)) (t - 1 - s)
              else A N x c d s i (t - 1)) else 0)
        else if t = N.Tpipe - 1 ∧ i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
        else 0)
  (hord : ∀ d t, (conPolicy N x c).order t d = q0 N x c d t)

lemma sum_split_batch (f : Fin n → ℝ) :
    ∑ i, f i = ∑ i ∈ bset c, f i + ∑ i ∈ Finset.univ.filter (fun i => ¬ c.batch i = true), f i := by
  unfold bset; rw [Finset.sum_filter_add_sum_filter_not]

include hdisp hord in
/-- Setup costs over a horizon. -/
lemma setups_total (hN : N.Standing) (hsS : ∀ i, c.s i ≤ c.S i) (hs0S : c.s0 ≤ c.S0)
    (hθ : ∀ d s i, 0 < θ d s i ∧ θ d s i < 1) (d : ℕ → DemandVec n) (T : ℕ) :
    ∑ t ∈ Finset.range T, (N.K0 * (if 0 < (conPolicy N x c).order t d then 1 else 0)
        + ∑ i, N.K i * (if 0 < (conPolicy N x c).dispatch t d i then 1 else 0))
      ≤ ∑ t ∈ Finset.range T, (if act N x c d t then
            N.K0 * (if 0 < q0 N x c d t then 1 else 0)
              + ∑ i ∈ Finset.univ.filter (fun i => ¬ c.batch i = true), N.K i
          else ∑ i, N.K i)
        + ∑ s ∈ Finset.range T, ∑ i ∈ bset c,
            N.K i * (if 0 < q N x c d s i then Ncnt (θ d s i) else 0) := by
  have hK0 := hN.K0_nonneg
  have hK := hN.K_nonneg
  have hpt : ∀ t, N.K0 * (if 0 < (conPolicy N x c).order t d then 1 else 0)
        + ∑ i, N.K i * (if 0 < (conPolicy N x c).dispatch t d i then 1 else 0)
      ≤ (if act N x c d t then N.K0 * (if 0 < q0 N x c d t then 1 else 0)
            + ∑ i ∈ Finset.univ.filter (fun i => ¬ c.batch i = true), N.K i
          else ∑ i, N.K i)
        + ∑ i ∈ bset c, N.K i * (if act N x c d t ∧ 0 < (conPolicy N x c).dispatch t d i then 1
            else 0) := by
    intro t
    rw [hord d t]
    have hind : ∀ i, N.K i * (if 0 < (conPolicy N x c).dispatch t d i then (1 : ℝ) else 0)
        ≤ N.K i := fun i => by
      split_ifs <;> nlinarith [hK i]
    have hind0 : ∀ i, 0 ≤ N.K i * (if act N x c d t ∧ 0 < (conPolicy N x c).dispatch t d i then
        (1 : ℝ) else 0) := fun i => by split_ifs <;> nlinarith [hK i]
    by_cases ha : act N x c d t
    · rw [if_pos ha, sum_split_batch c]
      have h1 : ∑ i ∈ bset c, N.K i * (if 0 < (conPolicy N x c).dispatch t d i then (1 : ℝ) else 0)
          = ∑ i ∈ bset c, N.K i * (if act N x c d t ∧ 0 < (conPolicy N x c).dispatch t d i then
              (1 : ℝ) else 0) := Finset.sum_congr rfl fun i _ => by
        by_cases hd : 0 < (conPolicy N x c).dispatch t d i
        · rw [if_pos hd, if_pos ⟨ha, hd⟩]
        · rw [if_neg hd, if_neg (fun h => hd h.2)]
      have h2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ c.batch i = true),
            N.K i * (if 0 < (conPolicy N x c).dispatch t d i then (1 : ℝ) else 0)
          ≤ ∑ i ∈ Finset.univ.filter (fun i => ¬ c.batch i = true), N.K i :=
        Finset.sum_le_sum fun i _ => hind i
      rw [h1]; linarith
    · rw [if_neg ha, q0_zero N x c d t ha]
      simp only [lt_irrefl, if_false, mul_zero, zero_add]
      have h2 : ∑ i, N.K i * (if 0 < (conPolicy N x c).dispatch t d i then (1 : ℝ) else 0)
          ≤ ∑ i, N.K i := Finset.sum_le_sum fun i _ => hind i
      have h3 : 0 ≤ ∑ i ∈ bset c, N.K i * (if act N x c d t ∧
          0 < (conPolicy N x c).dispatch t d i then (1 : ℝ) else 0) :=
        Finset.sum_nonneg fun i _ => hind0 i
      linarith
  refine le_trans (Finset.sum_le_sum fun t _ => hpt t) ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add le_rfl ?_
  rw [Finset.sum_comm]
  rw [Finset.sum_comm (s := Finset.range T)]
  refine Finset.sum_le_sum fun i hi => ?_
  have hb : c.batch i = true := by simpa [bset] using hi
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (hK i)
  have := setup_count N x c θ hdisp hsS hs0S hθ d i hb T
  refine le_trans this (le_of_eq (Finset.sum_congr rfl fun s _ => ?_))
  unfold Ncnt; rfl

/-- The sum shifted by a lead time. -/
lemma shift_sum_le (G : ℕ → ℝ) (hG : ∀ t, 0 ≤ G t) (L T : ℕ) :
    ∑ t ∈ Finset.range T, G t
      ≤ ∑ t ∈ Finset.range L, G t + ∑ t ∈ Finset.range T, G (t + L) := by
  rcases le_or_gt T L with h | h
  · have h1 : ∑ t ∈ Finset.range T, G t ≤ ∑ t ∈ Finset.range L, G t :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 h) fun t _ _ => hG t
    have h2 : 0 ≤ ∑ t ∈ Finset.range T, G (t + L) := Finset.sum_nonneg fun t _ => hG _
    linarith
  · obtain ⟨m, rfl⟩ : ∃ m, T = L + m := ⟨T - L, by omega⟩
    rw [Finset.sum_range_add]
    have h3 : ∑ t ∈ Finset.range m, G (L + t) ≤ ∑ t ∈ Finset.range (L + m), G (t + L) := by
      calc ∑ t ∈ Finset.range m, G (L + t) = ∑ t ∈ Finset.range m, G (t + L) :=
            Finset.sum_congr rfl fun t _ => by rw [add_comm]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
            fun t _ _ => hG _
    linarith

include hdisp hord in
/-- Physical costs over a horizon. -/
lemma phys_total (hN : N.Standing) (hx : x.Valid) (hsS : ∀ i, c.s i ≤ c.S i) (hs0 : 0 ≤ c.s0)
    (hs0S : c.s0 ≤ c.S0) (d : ℕ → DemandVec n) (T : ℕ) :
    ∑ t ∈ Finset.range T, (N.h * Policy.whStock N x (conPolicy N x c).toPolicy () d t
        + ∑ i, cH N i (Policy.netInv N x (conPolicy N x c).toPolicy () d i t))
      ≤ ∑ i, ∑ t ∈ Finset.range (N.L i), cH N i (Policy.netInv N x (conPolicy N x c).toPolicy () d i t)
        + ∑ t ∈ Finset.range T, ((if act N x c d t then
              whLoss N.h N.p (V N x c d t - Cq N x c d t - X N x c d t)
                + ∑ i, N.h * (c.S i - Ph N x c d t i)
            else N.h * W0 N x)
          + ∑ i, cH N i (Pos N x c d t i - Dblk N d t i))
        + (N.h + N.p) * ∑ r ∈ Finset.range T, ∑ i, ∑ k ∈ Finset.range (N.L0 + 1),
            max (A N x c d r i (r + k) - sh N x c θ d r i (r + k) - X N x c d (r + k)) 0 := by
  have hh := hN.h_pos.le
  have hp := hN.p_pos.le
  -- shift the retailer costs by the lead times
  have hshift : ∀ i, ∑ t ∈ Finset.range T, cH N i (Policy.netInv N x (conPolicy N x c).toPolicy () d i t)
      ≤ ∑ t ∈ Finset.range (N.L i), cH N i (Policy.netInv N x (conPolicy N x c).toPolicy () d i t)
        + ∑ t ∈ Finset.range T, cH N i (rP N x c d t i - Dblk N d t i) := fun i => by
    have := shift_sum_le (fun t => cH N i (Policy.netInv N x (conPolicy N x c).toPolicy () d i t))
      (fun t => cH_nonneg N hN i _) (N.L i) T
    simp only [netInv_shift N x c d i] at this
    exact this
  have hres := res_reindex N x c θ hsS hs0 hs0S d T
  have hR0 : ∀ t, 0 ≤ ∑ r ∈ Finset.range (t + 1), ∑ i,
      max (A N x c d r i t - sh N x c θ d r i t - X N x c d t) 0 := fun t =>
    Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun i _ => le_max_right _ _
  have hpt : ∀ t, N.h * Policy.whStock N x (conPolicy N x c).toPolicy () d t
        + ∑ i, cH N i (rP N x c d t i - Dblk N d t i)
      ≤ ((if act N x c d t then
              whLoss N.h N.p (V N x c d t - Cq N x c d t - X N x c d t)
                + ∑ i, N.h * (c.S i - Ph N x c d t i)
            else N.h * W0 N x)
          + ∑ i, cH N i (Pos N x c d t i - Dblk N d t i))
        + (N.h + N.p) * ∑ r ∈ Finset.range (t + 1), ∑ i,
            max (A N x c d r i t - sh N x c θ d r i t - X N x c d t) 0 := by
    intro t
    by_cases ha : act N x c d t
    · have hp' := path_run N x c θ hdisp hord hN hsS hs0S d t ha
      rw [if_pos ha]
      have e : ∀ i, Pos N x c d t i = Ph N x c d t i := fun i => by unfold Pos; rw [if_pos ha]
      simp only [e]
      unfold Dblk
      rw [Finset.sum_add_distrib] at hp'
      linarith
    · rw [if_neg ha]
      have e : ∀ i, Pos N x c d t i = rP N x c d t i := fun i => by unfold Pos; rw [if_neg ha]
      simp only [e]
      have hw := (whStock_prep N x c θ hdisp hord hx hs0S d t ha).2
      have := mul_le_mul_of_nonneg_left hw hh
      have := mul_nonneg (by linarith : (0:ℝ) ≤ N.h + N.p) (hR0 t)
      linarith
  calc ∑ t ∈ Finset.range T, (N.h * Policy.whStock N x (conPolicy N x c).toPolicy () d t
        + ∑ i, cH N i (Policy.netInv N x (conPolicy N x c).toPolicy () d i t))
      = ∑ t ∈ Finset.range T, N.h * Policy.whStock N x (conPolicy N x c).toPolicy () d t
        + ∑ i, ∑ t ∈ Finset.range T, cH N i (Policy.netInv N x (conPolicy N x c).toPolicy () d i t) := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ ∑ t ∈ Finset.range T, N.h * Policy.whStock N x (conPolicy N x c).toPolicy () d t
        + ∑ i, (∑ t ∈ Finset.range (N.L i), cH N i (Policy.netInv N x (conPolicy N x c).toPolicy () d i t)
          + ∑ t ∈ Finset.range T, cH N i (rP N x c d t i - Dblk N d t i)) := by
        gcongr with i; exact hshift i
    _ = ∑ i, ∑ t ∈ Finset.range (N.L i), cH N i (Policy.netInv N x (conPolicy N x c).toPolicy () d i t)
        + ∑ t ∈ Finset.range T, (N.h * Policy.whStock N x (conPolicy N x c).toPolicy () d t
          + ∑ i, cH N i (rP N x c d t i - Dblk N d t i)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm (s := Finset.univ)]
        ring
    _ ≤ ∑ i, ∑ t ∈ Finset.range (N.L i), cH N i (Policy.netInv N x (conPolicy N x c).toPolicy () d i t)
        + ∑ t ∈ Finset.range T, (((if act N x c d t then
              whLoss N.h N.p (V N x c d t - Cq N x c d t - X N x c d t)
                + ∑ i, N.h * (c.S i - Ph N x c d t i)
            else N.h * W0 N x)
          + ∑ i, cH N i (Pos N x c d t i - Dblk N d t i))
          + (N.h + N.p) * ∑ r ∈ Finset.range (t + 1), ∑ i,
            max (A N x c d r i t - sh N x c θ d r i t - X N x c d t) 0) :=
        add_le_add le_rfl (Finset.sum_le_sum fun t _ => hpt t)
    _ ≤ _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        have := mul_le_mul_of_nonneg_left hres (by linarith : (0:ℝ) ≤ N.h + N.p)
        linarith

lemma Zexp_nonneg (hN : N.Standing) (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) (θ' : ℝ) :
    0 ≤ Zexp N x c d s i θ' := by
  unfold Zexp
  have := hN.h_pos; have := hN.p_pos
  exact add_nonneg (mul_nonneg (hN.K_nonneg i) (Ncnt_nonneg θ'))
    (mul_nonneg (by linarith) (Finset.sum_nonneg fun k _ => le_max_right _ _))

/-- Setups and reserves of all requests: proxies of ordinary requests and the initial requests. -/
lemma proxy_split (hN : N.Standing) (hsS : ∀ i, c.s i ≤ c.S i) (hs0S : c.s0 ≤ c.S0)
    (d : ℕ → DemandVec n) (T : ℕ) :
    ∑ s ∈ Finset.range T, ∑ i ∈ bset c,
        N.K i * (if 0 < q N x c d s i then Ncnt (θ d s i) else 0)
      + (N.h + N.p) * ∑ r ∈ Finset.range T, ∑ i, ∑ k ∈ Finset.range (N.L0 + 1),
          max (A N x c d r i (r + k) - sh N x c θ d r i (r + k) - X N x c d (r + k)) 0
      ≤ ∑ s ∈ Finset.range T, ∑ i, (if ord N x c d s i then Zexp N x c d s i (θ d s i) else 0)
        + ∑ t ∈ Finset.range T, (if start N x c d t then
            ∑ i, (3 * N.K i + (N.h + N.p) * ((N.L0 + 1 : ℝ) * q N x c d t i)) else 0) := by
  have hh := hN.h_pos.le; have hp := hN.p_pos.le
  have hK := hN.K_nonneg
  have e1 : ∀ s, ∑ i ∈ bset c, N.K i * (if 0 < q N x c d s i then Ncnt (θ d s i) else 0)
      = ∑ i, (if c.batch i = true then N.K i * (if 0 < q N x c d s i then Ncnt (θ d s i) else 0)
          else 0) := fun s => by
    unfold bset; rw [Finset.sum_filter]
  have e2 : ∀ t, (if start N x c d t then
        ∑ i, (3 * N.K i + (N.h + N.p) * ((N.L0 + 1 : ℝ) * q N x c d t i)) else 0)
      = ∑ i, (if start N x c d t then
          3 * N.K i + (N.h + N.p) * ((N.L0 + 1 : ℝ) * q N x c d t i) else 0) := fun t => by
    split_ifs <;> simp
  simp_rw [e1, e2]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s hs => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hres0 : ∀ k, 0 ≤ max (A N x c d s i (s + k) - sh N x c θ d s i (s + k)
      - X N x c d (s + k)) 0 := fun k => le_max_right _ _
  have hRHS0 : 0 ≤ (if ord N x c d s i then Zexp N x c d s i (θ d s i) else 0)
      + (if start N x c d s then 3 * N.K i + (N.h + N.p) * ((N.L0 + 1 : ℝ) * q N x c d s i)
        else 0) := by
    refine add_nonneg ?_ ?_
    · split_ifs; exacts [Zexp_nonneg N x c hN d s i _, le_rfl]
    · have := q_nonneg N x c hsS d s i
      split_ifs
      · have := hK i; positivity
      · exact le_rfl
  rcases eq_or_lt_of_le (q_nonneg N x c hsS d s i) with hq | hq
  · -- no request
    have hA : ∀ k, A N x c d s i k = 0 := fun k =>
      le_antisymm ((A_le_q N x c hsS d s i k).trans hq.symm.le) (A_nonneg N x c d s i k)
    have hz : ∀ k, max (A N x c d s i (s + k) - sh N x c θ d s i (s + k) - X N x c d (s + k)) 0
        = 0 := fun k => by
      have h1 := sh_props N x c θ hsS hs0S d s i (s + k) (by omega)
      rw [hA] at h1
      have : sh N x c θ d s i (s + k) = 0 := le_antisymm h1.2.1 h1.1
      rw [hA, this]
      exact max_eq_right (by linarith [X_nonneg N x c hsS d (s + k)])
    have hnq : ¬ 0 < q N x c d s i := by rw [← hq]; exact lt_irrefl 0
    have hL : (if c.batch i = true then N.K i * (if 0 < q N x c d s i then Ncnt (θ d s i) else 0)
        else 0) = 0 := by
      rw [if_neg hnq, mul_zero, ite_self]
    have hR : ∑ k ∈ Finset.range (N.L0 + 1), (N.h + N.p) * max (A N x c d s i (s + k)
        - sh N x c θ d s i (s + k) - X N x c d (s + k)) 0 = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [hz k, mul_zero]
    rw [hL, hR, add_zero]
    exact hRHS0
  · by_cases hb : c.batch i = true
    · rw [if_pos hb, if_pos hq]
      by_cases ho : ord N x c d s i
      · rw [if_pos ho]
        have hst : ∀ k, sh N x c θ d s i (s + k)
            = shippedPath (q N x c d s i) (θ d s i) (fun k => A N x c d s i (s + k)) k := by
          intro k; unfold sh; rw [if_pos hb, Nat.add_sub_cancel_left]
        simp_rw [hst]
        have : 0 ≤ (if start N x c d s then 3 * N.K i + (N.h + N.p) * ((N.L0 + 1 : ℝ) *
            q N x c d s i) else 0) := by
          split_ifs
          · have := hK i; positivity
          · exact le_rfl
        unfold Zexp
        rw [Finset.mul_sum]
        linarith
      · rw [if_neg ho]
        have hact : act N x c d s := by
          by_contra h; rw [q_zero N x c d s h i] at hq; exact lt_irrefl 0 hq
        have hstart : start N x c d s := by
          refine ⟨hact, fun h => ho ⟨?_, h, hq, hb⟩⟩
          have := (act_time N x c d s hact).1; omega
        rw [if_pos hstart, zero_add]
        have hk : ∀ k, max (A N x c d s i (s + k) - sh N x c θ d s i (s + k) - X N x c d (s + k)) 0
            ≤ q N x c d s i := fun k => by
          have h1 := sh_props N x c θ hsS hs0S d s i (s + k) (by omega)
          have h2 := A_le_q N x c hsS d s i (s + k)
          have h3 := X_nonneg N x c hsS d (s + k)
          exact max_le (by linarith [h1.1]) hq.le
        have hsum : ∑ k ∈ Finset.range (N.L0 + 1), (N.h + N.p) * max (A N x c d s i (s + k)
            - sh N x c θ d s i (s + k) - X N x c d (s + k)) 0
            ≤ (N.h + N.p) * ((N.L0 + 1 : ℝ) * q N x c d s i) := by
          rw [← Finset.mul_sum]
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          calc _ ≤ ∑ _k ∈ Finset.range (N.L0 + 1), q N x c d s i := Finset.sum_le_sum fun k _ => hk k
            _ = _ := by simp
        have := mul_le_mul_of_nonneg_left (Ncnt_le (θ d s i)) (hK i)
        linarith
    · rw [if_neg hb]
      have hz : ∀ k, max (A N x c d s i (s + k) - sh N x c θ d s i (s + k) - X N x c d (s + k)) 0
          = 0 := fun k => by
        unfold sh; rw [if_neg hb, sub_self, zero_sub]
        exact max_eq_right (by linarith [X_nonneg N x c hsS d (s + k)])
      simp only [hz, mul_zero, Finset.sum_const_zero, add_zero, zero_add]
      exact hRHS0

include hdisp hord in
/-- The pathwise decomposition of the total cost over a horizon. -/
lemma cost_path (hN : N.Standing) (hx : x.Valid) (hsS : ∀ i, c.s i ≤ c.S i) (hs0 : 0 ≤ c.s0)
    (hs0S : c.s0 ≤ c.S0) (hθ : ∀ d s i, 0 < θ d s i ∧ θ d s i < 1) (d : ℕ → DemandVec n)
    (T : ℕ) :
    ∑ t ∈ Finset.range T, Policy.periodCost N x (conPolicy N x c).toPolicy () d t
      ≤ ∑ i, ∑ t ∈ Finset.range (N.L i),
            cH N i (Policy.netInv N x (conPolicy N x c).toPolicy () d i t)
        + ∑ t ∈ Finset.range T, (if act N x c d t then
            N.K0 * (if 0 < q0 N x c d t then 1 else 0)
              + ∑ i ∈ Finset.univ.filter (fun i => ¬ c.batch i = true), N.K i
          else ∑ i, N.K i)
        + ∑ t ∈ Finset.range T, ((if act N x c d t then
              whLoss N.h N.p (V N x c d t - Cq N x c d t - X N x c d t)
                + ∑ i, N.h * (c.S i - Ph N x c d t i)
            else N.h * W0 N x)
          + ∑ i, cH N i (Pos N x c d t i - Dblk N d t i))
        + ∑ t ∈ Finset.range T, (if start N x c d t then
            ∑ i, (3 * N.K i + (N.h + N.p) * ((N.L0 + 1 : ℝ) * q N x c d t i)) else 0)
        + ∑ s ∈ Finset.range T, ∑ i, (if ord N x c d s i then Zexp N x c d s i (θ d s i) else 0) := by
  have hS := setups_total N x c θ hdisp hord hN hsS hs0S hθ d T
  have hP := phys_total N x c θ hdisp hord hN hx hsS hs0 hs0S d T
  have hX := proxy_split N x c θ hN hsS hs0S d T
  have e : ∑ t ∈ Finset.range T, Policy.periodCost N x (conPolicy N x c).toPolicy () d t
      = ∑ t ∈ Finset.range T, (N.K0 * (if 0 < (conPolicy N x c).order t d then 1 else 0)
          + ∑ i, N.K i * (if 0 < (conPolicy N x c).dispatch t d i then 1 else 0))
        + ∑ t ∈ Finset.range T, (N.h * Policy.whStock N x (conPolicy N x c).toPolicy () d t
          + ∑ i, cH N i (Policy.netInv N x (conPolicy N x c).toPolicy () d i t)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h1 : (conPolicy N x c).toPolicy.order t () d = (conPolicy N x c).order t d := rfl
    have h2 : ∀ i, (conPolicy N x c).toPolicy.dispatch t () d i
        = (conPolicy N x c).dispatch t d i := fun i => rfl
    unfold Policy.periodCost cH
    rw [h1]
    simp only [h2]
    rw [Finset.sum_add_distrib]
    ring
  rw [e]
  linarith

end path4

end OWMR.Asm

end Part4

section Part5

/-! Assembly, part 5: past dependence and measurability of the explicit processes. -/

open MeasureTheory
open scoped ENNReal NNReal


namespace OWMR.Asm

variable {n : ℕ} (N : Network n) (x : InitState n) (c : ConChoice n)

lemma meas_coord (t : ℕ) (i : Fin n) :
    Measurable fun d : ℕ → DemandVec n => ((d t i : ℝ≥0) : ℝ) :=
  ((measurable_pi_apply i).comp (measurable_pi_apply t)).coe_nnreal_real

lemma meas_dsum (t : ℕ) (i : Fin n) :
    Measurable fun d : ℕ → DemandVec n => ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) :=
  Finset.measurable_sum _ fun s _ => meas_coord s i

lemma dsum_dep (t : ℕ) (i : Fin n) (d d' : ℕ → DemandVec n) (h : ∀ r < t, d r = d' r) :
    ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) = ∑ s ∈ Finset.range t, ((d' s i : ℝ≥0) : ℝ) :=
  Finset.sum_congr rfl fun s hs => by rw [h s (Finset.mem_range.1 hs)]

lemma act_dep (t : ℕ) (d d' : ℕ → DemandVec n) (h : ∀ r < t, d r = d' r) :
    act N x c d t ↔ act N x c d' t := by
  unfold act
  simp only [dsum_dep t _ d d' h]

lemma act_meas (t : ℕ) : MeasurableSet {d : ℕ → DemandVec n | act N x c d t} := by
  unfold act
  have : {d : ℕ → DemandVec n | N.Tpipe - 1 + max 1 (N.L c.sendTo) ≤ t ∧ ∀ i,
      x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
        + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0)
        - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) ≤ c.S i}
      = {_d | N.Tpipe - 1 + max 1 (N.L c.sendTo) ≤ t} ∩ ⋂ i, {d | x.I i
        + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
        + (if i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s else 0)
        - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) ≤ c.S i} := by
    ext d; simp
  rw [this]
  exact (MeasurableSet.const _).inter (MeasurableSet.iInter fun i =>
    measurableSet_le (measurable_const.sub (meas_dsum t i)) measurable_const)

lemma Yp_dep : ∀ (t : ℕ) (d d' : ℕ → DemandVec n), (∀ r < t, d r = d' r) →
    Yp N x c d t = Yp N x c d' t
  | 0, _, _, _ => rfl
  | t + 1, d, d', h => by
    simp only [Yp]
    rw [Yp_dep t d d' (fun r hr => h r (by omega)), h t (by omega)]
    by_cases ha : act N x c d t
    · have ha' := (act_dep N x c t d d' (fun r hr => h r (by omega))).1 ha
      simp only [ha, ha', true_and]
    · have ha' : ¬ act N x c d' t := fun h' =>
        ha ((act_dep N x c t d d' (fun r hr => h r (by omega))).2 h')
      simp only [ha, ha', false_and, if_false]

lemma Yp_meas : ∀ t, Measurable fun d : ℕ → DemandVec n => Yp N x c d t
  | 0 => measurable_const
  | t + 1 => by
    simp only [Yp]
    exact Measurable.sub (Measurable.ite ((act_meas N x c t).inter
      (measurableSet_le (Yp_meas t) measurable_const)) measurable_const (Yp_meas t))
      (Finset.measurable_sum _ fun i _ => meas_coord t i)

lemma Ph_dep : ∀ (t : ℕ) (d d' : ℕ → DemandVec n), (∀ r < t, d r = d' r) →
    ∀ i, Ph N x c d t i = Ph N x c d' t i
  | 0, _, _, _, _ => rfl
  | t + 1, d, d', h, i => by
    simp only [Ph]
    have h2 := act_dep N x c t d d' (fun r hr => h r (by omega))
    rw [Ph_dep t d d' (fun r hr => h r (by omega)) i, h t (by omega)]
    by_cases hb : act N x c d t
    · simp only [hb, h2.1 hb, if_true]
    · have hb' : ¬ act N x c d' t := fun h' => hb (h2.2 h')
      simp only [hb, hb', if_false]

lemma Ph_meas : ∀ t i, Measurable fun d : ℕ → DemandVec n => Ph N x c d t i
  | 0, _ => measurable_const
  | t + 1, i => by
    simp only [Ph]
    exact Measurable.ite (act_meas N x c t)
      (Measurable.ite (measurableSet_le ((Ph_meas t i).sub (meas_coord t i)) measurable_const)
        measurable_const ((Ph_meas t i).sub (meas_coord t i))) measurable_const

lemma q_dep (t : ℕ) (d d' : ℕ → DemandVec n) (h : ∀ r < t, d r = d' r) (i : Fin n) :
    q N x c d t i = q N x c d' t i := by
  unfold q
  have h1 := act_dep N x c t d d' h
  have h2 := act_dep N x c (t - 1) d d' (fun r hr => h r (by omega))
  by_cases ha : act N x c d t
  · rw [if_pos ha, if_pos (h1.1 ha)]
    by_cases hb : t = 0 ∨ ¬ act N x c d (t - 1)
    · have hb' : t = 0 ∨ ¬ act N x c d' (t - 1) := by
        rcases hb with hb | hb
        · exact Or.inl hb
        · exact Or.inr fun h' => hb (h2.2 h')
      rw [if_pos hb, if_pos hb', dsum_dep t i d d' h]
    · push Not at hb
      have hb' : ¬ (t = 0 ∨ ¬ act N x c d' (t - 1)) := by
        push Not; exact ⟨hb.1, h2.1 hb.2⟩
      rw [if_neg (by push Not; exact hb), if_neg hb',
        Ph_dep N x c (t - 1) d d' (fun r hr => h r (by omega)) i, h (t - 1) (by omega)]
  · rw [if_neg ha, if_neg (fun h' => ha (h1.2 h'))]

lemma q_meas (t : ℕ) (i : Fin n) : Measurable fun d : ℕ → DemandVec n => q N x c d t i := by
  unfold q
  refine Measurable.ite (act_meas N x c t) ?_ measurable_const
  have hs : MeasurableSet {d : ℕ → DemandVec n | t = 0 ∨ ¬ act N x c d (t - 1)} :=
    (MeasurableSet.const _).union (act_meas N x c (t - 1)).compl
  refine Measurable.ite hs (measurable_const.sub ((measurable_const).sub (meas_dsum t i))) ?_
  exact Measurable.ite (measurableSet_le ((Ph_meas N x c (t - 1) i).sub (meas_coord (t - 1) i))
    measurable_const) (measurable_const.sub ((Ph_meas N x c (t - 1) i).sub (meas_coord (t - 1) i)))
    measurable_const

lemma q0_dep (t : ℕ) (d d' : ℕ → DemandVec n) (h : ∀ r < t, d r = d' r) :
    q0 N x c d t = q0 N x c d' t := by
  unfold q0
  rw [Yp_dep N x c t d d' h]
  have h1 := act_dep N x c t d d' h
  by_cases ha : act N x c d t
  · simp only [ha, h1.1 ha, true_and]
  · have ha' : ¬ act N x c d' t := fun h' => ha (h1.2 h')
    simp only [ha, ha', false_and, if_false]

lemma q0_meas (t : ℕ) : Measurable fun d : ℕ → DemandVec n => q0 N x c d t := by
  unfold q0
  exact Measurable.ite ((act_meas N x c t).inter (measurableSet_le (Yp_meas N x c t)
    measurable_const)) (measurable_const.sub (Yp_meas N x c t)) measurable_const

lemma Ypost_dep (t : ℕ) (d d' : ℕ → DemandVec n) (h : ∀ r < t, d r = d' r) :
    Ypost N x c d t = Ypost N x c d' t := by
  rw [Ypost_eq, Ypost_eq, Yp_dep N x c t d d' h, q0_dep N x c t d d' h]

lemma Ypost_meas (t : ℕ) : Measurable fun d : ℕ → DemandVec n => Ypost N x c d t := by
  have : (fun d => Ypost N x c d t) = fun d => Yp N x c d t + q0 N x c d t := by
    funext d; exact Ypost_eq N x c d t
  rw [this]; exact (Yp_meas N x c t).add (q0_meas N x c t)

lemma V_meas (t : ℕ) : Measurable fun d : ℕ → DemandVec n => V N x c d t :=
  Finset.measurable_sum _ fun r _ => q0_meas N x c r

lemma Cq_meas (t : ℕ) : Measurable fun d : ℕ → DemandVec n => Cq N x c d t :=
  Finset.measurable_sum _ fun r _ => Finset.measurable_sum _ fun j _ => q_meas N x c r j

lemma X_meas (t : ℕ) : Measurable fun d : ℕ → DemandVec n => X N x c d t :=
  Finset.measurable_sum _ fun i _ => measurable_const.sub (Ph_meas N x c t i)

lemma X_dep (t : ℕ) (d d' : ℕ → DemandVec n) (h : ∀ r < t, d r = d' r) :
    X N x c d t = X N x c d' t := by
  unfold X; simp only [Ph_dep N x c t d d' h]

lemma ahead_meas (s : ℕ) (i : Fin n) : Measurable fun d : ℕ → DemandVec n => ahead N x c d s i :=
  (Finset.measurable_sum _ fun r _ => Finset.measurable_sum _ fun j _ => q_meas N x c r j).add
    (Finset.measurable_sum _ fun j _ => q_meas N x c s j)

lemma A_meas (s : ℕ) (i : Fin n) (t : ℕ) :
    Measurable fun d : ℕ → DemandVec n => A N x c d s i t := by
  have : (fun d => A N x c d s i t)
      = fun d => max 0 (min (q N x c d s i) (V N x c d t - ahead N x c d s i)) := by
    funext d; exact A_eq N x c d s i t
  rw [this]
  exact measurable_const.max ((q_meas N x c s i).min ((V_meas N x c t).sub (ahead_meas N x c s i)))

lemma A_dep (s : ℕ) (i : Fin n) (t : ℕ) (d d' : ℕ → DemandVec n)
    (h : ∀ r < s, d r = d' r) (ht : t + 1 - N.L0 ≤ s) :
    A N x c d s i t = A N x c d' s i t := by
  rw [A_eq, A_eq]
  have hq : ∀ r ≤ s, ∀ j, q N x c d r j = q N x c d' r j := fun r hr j =>
    q_dep N x c r d d' (fun r' hr' => h r' (by omega)) j
  have hV : V N x c d t = V N x c d' t := by
    unfold V
    exact Finset.sum_congr rfl fun r hr => q0_dep N x c r d d'
      (fun r' hr' => h r' (by simp at hr; omega))
  have hah : ahead N x c d s i = ahead N x c d' s i := by
    unfold ahead
    rw [Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun j _ =>
      hq r (by simp at hr; omega) j]
    rw [Finset.sum_congr rfl fun j _ => hq s le_rfl j]
  rw [hq s le_rfl i, hV, hah]

/-- The retailer position in preparation periods. -/
def rPp (d : ℕ → DemandVec n) (t : ℕ) (i : Fin n) : ℝ :=
  x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
    + (if N.Tpipe - 1 ≤ t ∧ i = c.sendTo then W0 N x else 0)
    - ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ)

/-- The charged positions, explicitly. -/
def Pos' (d : ℕ → DemandVec n) (t : ℕ) (i : Fin n) : ℝ :=
  if act N x c d t then Ph N x c d t i else rPp N x c d t i

lemma Pos'_dep (t : ℕ) (d d' : ℕ → DemandVec n) (h : ∀ r < t, d r = d' r) (i : Fin n) :
    Pos' N x c d t i = Pos' N x c d' t i := by
  unfold Pos' rPp
  have h1 := act_dep N x c t d d' h
  by_cases ha : act N x c d t
  · rw [if_pos ha, if_pos (h1.1 ha), Ph_dep N x c t d d' h i]
  · rw [if_neg ha, if_neg (fun h' => ha (h1.2 h')), dsum_dep t i d d' h]

lemma Pos'_meas (t : ℕ) (i : Fin n) : Measurable fun d : ℕ → DemandVec n => Pos' N x c d t i := by
  unfold Pos' rPp
  exact Measurable.ite (act_meas N x c t) (Ph_meas N x c t i)
    (measurable_const.sub (meas_dsum t i))

/-- Retailer pre-request positions (the start counts as being at the target). -/
def Xpre (d : ℕ → DemandVec n) (t : ℕ) (i : Fin n) : ℝ :=
  if 0 < t ∧ act N x c d (t - 1) then Ph N x c d (t - 1) i - ((d (t - 1) i : ℝ≥0) : ℝ) else c.S i

lemma Xpre_dep (t : ℕ) (d d' : ℕ → DemandVec n) (h : ∀ r < t, d r = d' r) (i : Fin n) :
    Xpre N x c d t i = Xpre N x c d' t i := by
  unfold Xpre
  have h1 := act_dep N x c (t - 1) d d' (fun r hr => h r (by omega))
  by_cases ha : 0 < t ∧ act N x c d (t - 1)
  · rw [if_pos ha, if_pos ⟨ha.1, h1.1 ha.2⟩, Ph_dep N x c (t - 1) d d' (fun r hr => h r (by omega)) i,
      h (t - 1) (by omega)]
  · rw [if_neg ha, if_neg (fun h' => ha ⟨h'.1, h1.2 h'.2⟩)]

lemma Xpre_meas (t : ℕ) (i : Fin n) : Measurable fun d : ℕ → DemandVec n => Xpre N x c d t i := by
  unfold Xpre
  exact Measurable.ite ((MeasurableSet.const _).inter (act_meas N x c (t - 1)))
    ((Ph_meas N x c (t - 1) i).sub (meas_coord (t - 1) i)) measurable_const

lemma Xpre_post (d : ℕ → DemandVec n) (t : ℕ) (h : act N x c d t) (i : Fin n) :
    (if Xpre N x c d t i ≤ c.s i then c.S i else Xpre N x c d t i) = Ph N x c d t i := by
  unfold Xpre
  by_cases ha : 0 < t ∧ act N x c d (t - 1)
  · rw [if_pos ha]
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    simp only [add_tsub_cancel_right] at ha ⊢
    simp only [Ph, if_pos ha.2]
  · rw [if_neg ha]
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by have := (act_time N x c d t h).1; omega⟩
    have : ¬ act N x c d t' := fun h' => ha ⟨by omega, by simpa using h'⟩
    simp only [Ph, if_neg this]
    split_ifs <;> rfl

lemma Xpre_order (hsS : ∀ i, c.s i ≤ c.S i) (d : ℕ → DemandVec n) (t : ℕ) (h : act N x c d t)
    (i : Fin n) :
    (Xpre N x c d t i ≤ c.s i ∧ Xpre N x c d t i < c.S i) ↔ (0 < t ∧ act N x c d (t - 1)
      ∧ 0 < q N x c d t i) := by
  unfold Xpre
  by_cases ha : 0 < t ∧ act N x c d (t - 1)
  · rw [if_pos ha]
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    simp only [add_tsub_cancel_right] at ha ⊢
    rw [q_ord N x c d t' ha.2 i]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by omega, ha.2, ?_⟩
      rw [if_pos h1]; linarith
    · rintro ⟨-, -, h3⟩
      by_cases h1 : Ph N x c d t' i - ((d t' i : ℝ≥0) : ℝ) ≤ c.s i
      · rw [if_pos h1] at h3; exact ⟨h1, by linarith⟩
      · rw [if_neg h1] at h3; exact absurd h3 (lt_irrefl 0)
  · rw [if_neg ha]
    constructor
    · rintro ⟨-, h2⟩; exact absurd h2 (lt_irrefl _)
    · rintro ⟨h1, h2, -⟩; exact absurd ⟨h1, h2⟩ ha

lemma Dblk_meas (t : ℕ) (i : Fin n) : Measurable fun d : ℕ → DemandVec n => Dblk N d t i :=
  Finset.measurable_sum _ fun j _ => meas_coord (t + j) i

end OWMR.Asm

end Part5

section Part6

/-! Assembly, part 6: independence of later demands (block lemma). -/

open MeasureTheory
open scoped ENNReal NNReal


namespace OWMR.Asm

section coord

variable {α : Type} [MeasurableSpace α] [Zero α]

lemma measurable_padHist' (N : ℕ) : Measurable (padHist N : (Fin N → α) → ℕ → α) := by
  refine measurable_pi_lambda _ fun t => ?_
  by_cases h : t < N
  · simp only [padHist, dif_pos h]
    exact measurable_pi_apply _
  · simp only [padHist, dif_neg h]
    exact measurable_const

omit [MeasurableSpace α] in
lemma padHist_insertNth_lt {M : ℕ} (i : Fin (M + 1)) (a b : α) (z : Fin M → α) (s : ℕ)
    (hs : s < i.val) :
    padHist (M + 1) (Fin.insertNth (α := fun _ => α) i a z) s
      = padHist (M + 1) (Fin.insertNth (α := fun _ => α) i b z) s := by
  have hsM : s < M + 1 := lt_trans hs i.2
  have hsM' : s < M := lt_of_lt_of_le hs (Nat.lt_succ_iff.1 i.2)
  simp only [padHist, dif_pos hsM]
  have he : (⟨s, hsM⟩ : Fin (M + 1)) = i.succAbove ⟨s, hsM'⟩ := by
    rw [Fin.succAbove_of_castSucc_lt]
    · rfl
    · simp [Fin.lt_def, hs]
  rw [he, Fin.insertNth_apply_succAbove (α := fun _ => α),
    Fin.insertNth_apply_succAbove (α := fun _ => α)]

omit [MeasurableSpace α] in
lemma padHist_insertNth_self {M : ℕ} (i : Fin (M + 1)) (a : α) (z : Fin M → α) :
    padHist (M + 1) (Fin.insertNth (α := fun _ => α) i a z) i.val = a := by
  simp only [padHist, dif_pos i.2]
  exact Fin.insertNth_apply_same (α := fun _ => α) i a z

/-- The `t`-th demand is independent of anything depending on the demands before `t`. -/
lemma lintegral_coord (μ : Measure α) [IsProbabilityMeasure μ]
    (N t : ℕ) (ht : t < N) (Φ : (ℕ → α) → α → ℝ≥0∞)
    (hΦ : Measurable fun p : (ℕ → α) × α => Φ p.1 p.2)
    (hdep : ∀ (d d' : ℕ → α) (a : α), (∀ s < t, d s = d' s) → Φ d a = Φ d' a) :
    ∫⁻ z, Φ (padHist N z) (padHist N z t) ∂(Measure.pi fun _ : Fin N => μ)
      = ∫⁻ z, ∫⁻ a, Φ (padHist N z) a ∂μ ∂(Measure.pi fun _ : Fin N => μ) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hD : Measurable fun z : Fin (M + 1) → α => padHist (M + 1) z := measurable_padHist' _
  set i : Fin (M + 1) := ⟨t, ht⟩ with hi
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) => μ) i
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => α) i with he
  have hsymm : ∀ p : α × (Fin M → α), e.symm p = Fin.insertNth (α := fun _ => α) i p.1 p.2 :=
    fun p => rfl
  have key : ∀ F : (Fin (M + 1) → α) → ℝ≥0∞,
      ∫⁻ z, F z ∂(Measure.pi fun _ : Fin (M + 1) => μ)
        = ∫⁻ p, F (e.symm p) ∂(μ.prod (Measure.pi fun _ : Fin M => μ)) := by
    intro F
    rw [← hmp.lintegral_comp_emb e.measurableEmbedding]
    simp only [MeasurableEquiv.symm_apply_apply]
  have hind : ∀ (a b : α) (z : Fin M → α) (c : α),
      Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i a z)) c
        = Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i b z)) c := by
    intro a b z c
    exact hdep _ _ c fun s hs => padHist_insertNth_lt i a b z s (by simpa [hi] using hs)
  have hins : Measurable fun p : α × (Fin M → α) => Fin.insertNth (α := fun _ => α) i p.1 p.2 :=
    e.symm.measurable
  have hG : Measurable fun p : α × (Fin M → α) =>
      Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i p.1 p.2)) p.1 :=
    hΦ.comp ((hD.comp hins).prodMk measurable_fst)
  rw [key, key]
  simp only [hsymm]
  have hl : ∀ p : α × (Fin M → α),
      padHist (M + 1) (Fin.insertNth (α := fun _ => α) i p.1 p.2) t = p.1 :=
    fun p => padHist_insertNth_self i p.1 p.2
  simp only [hl]
  rw [lintegral_prod_symm _ hG.aemeasurable]
  have hc : ∀ (a : α) (z : Fin M → α),
      ∫⁻ c, Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i a z)) c ∂μ
        = ∫⁻ c, Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i c z)) c ∂μ := fun a z =>
    lintegral_congr fun c => hind a c z c
  simp only [hc]
  have hH : Measurable fun z : Fin M → α =>
      ∫⁻ c, Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i c z)) c ∂μ :=
    Measurable.lintegral_prod_right' (f := fun p : (Fin M → α) × α =>
      Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i p.2 p.1)) p.2)
      (hΦ.comp ((hD.comp (hins.comp (measurable_snd.prodMk measurable_fst))).prodMk measurable_snd))
  have hprod := lintegral_prod (μ := μ) (ν := Measure.pi fun _ : Fin M => μ)
    (fun p : α × (Fin M → α) =>
      ∫⁻ c, Φ (padHist (M + 1) (Fin.insertNth (α := fun _ => α) i c p.2)) c ∂μ)
    (hH.comp measurable_snd).aemeasurable
  rw [hprod]
  simp only [lintegral_const, measure_univ, mul_one]

end coord

section blk

variable {α : Type} [MeasurableSpace α] [Zero α]

lemma block_insert {m : ℕ} (f : ℕ → α) (t : ℕ) :
    (fun j : Fin (m + 1) => f (t + j))
      = Fin.insertNth (α := fun _ => α) (Fin.last m) (f (t + m)) (fun j : Fin m => f (t + j)) := by
  funext j
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · simp only [Fin.insertNth_apply_same, Fin.val_last]
  · have : (Fin.castSucc j' : Fin (m + 1)) = (Fin.last m).succAbove j' := by
      rw [Fin.succAbove_last]
    rw [this, Fin.insertNth_apply_succAbove]
    simp [Fin.succAbove_last]

lemma lintegral_insert_last (μ : Measure α) [IsProbabilityMeasure μ] (m : ℕ)
    (F : (Fin (m + 1) → α) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ b, F b ∂(Measure.pi fun _ : Fin (m + 1) => μ)
      = ∫⁻ a, ∫⁻ b', F (Fin.insertNth (α := fun _ => α) (Fin.last m) a b')
          ∂(Measure.pi fun _ : Fin m => μ) ∂μ := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) (Fin.last m)
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) (Fin.last m) with he
  have hsymm : ∀ p : α × (Fin m → α), e.symm p = Fin.insertNth (α := fun _ => α) (Fin.last m) p.1 p.2 :=
    fun p => rfl
  have key : ∫⁻ z, F z ∂(Measure.pi fun _ : Fin (m + 1) => μ)
      = ∫⁻ p, F (e.symm p) ∂(μ.prod (Measure.pi fun _ : Fin m => μ)) := by
    rw [← hmp.lintegral_comp_emb e.measurableEmbedding]
    simp only [MeasurableEquiv.symm_apply_apply]
  rw [key, lintegral_prod (fun p : α × (Fin m → α) => F (e.symm p))
    ((hF.comp e.symm.measurable).aemeasurable)]
  rfl

/-- Later demands are independent of the past: a block of `m` demands from period `t`. -/
lemma lintegral_blk (μ : Measure α) [IsProbabilityMeasure μ] (N t : ℕ) :
    ∀ (m : ℕ), t + m ≤ N → ∀ (Φ : (ℕ → α) → (Fin m → α) → ℝ≥0∞),
      Measurable (fun p : (ℕ → α) × (Fin m → α) => Φ p.1 p.2) →
      (∀ (d d' : ℕ → α) (b : Fin m → α), (∀ s < t, d s = d' s) → Φ d b = Φ d' b) →
      ∫⁻ z, Φ (padHist N z) (fun j => padHist N z (t + j)) ∂(Measure.pi fun _ : Fin N => μ)
        = ∫⁻ z, ∫⁻ b, Φ (padHist N z) b ∂(Measure.pi fun _ : Fin m => μ)
            ∂(Measure.pi fun _ : Fin N => μ)
  | 0, _, Φ, hΦ, _ => by
    have hb : ∀ b : Fin 0 → α, b = fun j => j.elim0 := fun b => funext fun j => j.elim0
    have h1 : ∀ z : Fin N → α, (fun j : Fin 0 => padHist N z (t + j)) = fun j => j.elim0 :=
      fun z => hb _
    simp_rw [h1]
    refine lintegral_congr fun z => ?_
    have : ∀ b : Fin 0 → α, Φ (padHist N z) b = Φ (padHist N z) (fun j => j.elim0) := fun b => by
      rw [hb b]
    simp_rw [this]
    simp
  | m + 1, hm, Φ, hΦ, hdep => by
    have hD := measurable_padHist' (α := α) N
    have hblk : Measurable fun d : ℕ → α => fun j : Fin m => d (t + j) :=
      measurable_pi_lambda _ fun j => measurable_pi_apply _
    have hins : Measurable fun p : α × (Fin m → α) =>
        Fin.insertNth (α := fun _ => α) (Fin.last m) p.1 p.2 :=
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) (Fin.last m)).symm.measurable
    set Ψ : (ℕ → α) → α → ℝ≥0∞ := fun d a =>
      Φ d (Fin.insertNth (α := fun _ => α) (Fin.last m) a (fun j : Fin m => d (t + j))) with hΨ
    have hΨm : Measurable fun p : (ℕ → α) × α => Ψ p.1 p.2 :=
      hΦ.comp (measurable_fst.prodMk (hins.comp (measurable_snd.prodMk (hblk.comp measurable_fst))))
    have hΨd : ∀ (d d' : ℕ → α) (a : α), (∀ s < t + m, d s = d' s) → Ψ d a = Ψ d' a := by
      intro d d' a h
      simp only [hΨ]
      have e : (fun j : Fin m => d (t + j)) = fun j : Fin m => d' (t + j) :=
        funext fun j => h _ (by omega)
      rw [e]
      exact hdep d d' _ fun s hs => h s (by omega)
    have h1 := lintegral_coord μ N (t + m) (by omega) Ψ hΨm hΨd
    have e1 : ∀ z : Fin N → α, Φ (padHist N z) (fun j : Fin (m + 1) => padHist N z (t + j))
        = Ψ (padHist N z) (padHist N z (t + m)) := fun z => by
      simp only [hΨ]; rw [block_insert (padHist N z) t]
    simp_rw [e1]
    rw [h1]
    -- inner step for each value of the last coordinate
    have hIH : ∀ a : α, ∫⁻ z, Ψ (padHist N z) a ∂(Measure.pi fun _ : Fin N => μ)
        = ∫⁻ z, ∫⁻ b', Φ (padHist N z) (Fin.insertNth (α := fun _ => α) (Fin.last m) a b')
          ∂(Measure.pi fun _ : Fin m => μ) ∂(Measure.pi fun _ : Fin N => μ) := fun a =>
      lintegral_blk μ N t m (by omega)
        (fun d b' => Φ d (Fin.insertNth (α := fun _ => α) (Fin.last m) a b'))
        (hΦ.comp (measurable_fst.prodMk (hins.comp (measurable_const.prodMk measurable_snd))))
        (fun d d' b' h => hdep d d' _ h)
    have hsw1 : ∫⁻ z, ∫⁻ a, Ψ (padHist N z) a ∂μ ∂(Measure.pi fun _ : Fin N => μ)
        = ∫⁻ a, ∫⁻ z, Ψ (padHist N z) a ∂(Measure.pi fun _ : Fin N => μ) ∂μ :=
      lintegral_lintegral_swap ((hΨm.comp ((hD.comp measurable_fst).prodMk measurable_snd)).aemeasurable)
    rw [hsw1]
    simp_rw [hIH]
    have hm3 : Measurable fun p : α × ((Fin N → α) × (Fin m → α)) =>
        Φ (padHist N p.2.1) (Fin.insertNth (α := fun _ => α) (Fin.last m) p.1 p.2.2) :=
      hΦ.comp ((hD.comp (measurable_fst.comp measurable_snd)).prodMk
        (hins.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))))
    have hsw2 : ∫⁻ a, ∫⁻ z, ∫⁻ b', Φ (padHist N z) (Fin.insertNth (α := fun _ => α) (Fin.last m) a b')
          ∂(Measure.pi fun _ : Fin m => μ) ∂(Measure.pi fun _ : Fin N => μ) ∂μ
        = ∫⁻ z, ∫⁻ a, ∫⁻ b', Φ (padHist N z) (Fin.insertNth (α := fun _ => α) (Fin.last m) a b')
          ∂(Measure.pi fun _ : Fin m => μ) ∂μ ∂(Measure.pi fun _ : Fin N => μ) := by
      refine lintegral_lintegral_swap ?_
      exact (Measurable.lintegral_prod_right' (f := fun p : (α × (Fin N → α)) × (Fin m → α) =>
        Φ (padHist N p.1.2) (Fin.insertNth (α := fun _ => α) (Fin.last m) p.1.1 p.2))
        (hΦ.comp ((hD.comp (measurable_snd.comp measurable_fst)).prodMk
          (hins.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))))).aemeasurable
    rw [hsw2]
    refine lintegral_congr fun z => ?_
    rw [lintegral_insert_last μ m (Φ (padHist N z)) (hΦ.comp (measurable_const.prodMk measurable_id))]

/-- Restricting `N` i.i.d. coordinates to the first `T`. -/
lemma pi_map_restrict (μ : Measure α) [IsProbabilityMeasure μ] (T N : ℕ) (h : T ≤ N) :
    (Measure.pi fun _ : Fin N => μ).map (fun z : Fin N → α => fun j : Fin T => z (Fin.castLE h j))
      = Measure.pi fun _ : Fin T => μ := by
  have hρ : Measurable fun z : Fin N → α => fun j : Fin T => z (Fin.castLE h j) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply _
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hρ (MeasurableSet.univ_pi hs)]
  set s' : Fin N → Set α := fun k => if hk : k.val < T then s ⟨k, hk⟩ else Set.univ with hs'
  have hpre : (fun z : Fin N → α => fun j : Fin T => z (Fin.castLE h j)) ⁻¹' Set.univ.pi s
      = Set.univ.pi s' := by
    ext z
    simp only [Set.mem_preimage, Set.mem_univ_pi, hs']
    constructor
    · intro hz k
      split_ifs with hk
      · exact hz ⟨k, hk⟩
      · exact Set.mem_univ _
    · intro hz j
      have := hz (Fin.castLE h j)
      simp only [Fin.coe_castLE, j.2, dif_pos] at this
      exact this
  rw [hpre, Measure.pi_pi]
  set f : ℕ → ℝ≥0∞ := fun k => if hk : k < T then μ (s ⟨k, hk⟩) else 1 with hf
  have e1 : ∏ k : Fin N, μ (s' k) = ∏ k ∈ Finset.range N, f k := by
    rw [← Fin.prod_univ_eq_prod_range f N]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [hs', hf]
    split_ifs <;> simp
  have e2 : ∏ j : Fin T, μ (s j) = ∏ k ∈ Finset.range T, f k := by
    rw [← Fin.prod_univ_eq_prod_range f T]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [hf, dif_pos j.2]
  rw [e1, e2, ← Finset.prod_range_mul_prod_Ico f h]
  rw [Finset.prod_eq_one (s := Finset.Ico T N) fun k hk => by
    simp only [hf, Finset.mem_Ico] at hk ⊢; rw [dif_neg (by omega)], mul_one]

/-- A cost depending on the first `T` periods has no larger expectation on a longer horizon. -/
lemma horizon_le (μ : Measure α) [IsProbabilityMeasure μ] (T N : ℕ) (h : T ≤ N)
    (G : (ℕ → α) → ℝ≥0∞) (hG : ∀ d d' : ℕ → α, (∀ r < T, d r = d' r) → G d = G d') :
    ∫⁻ z, G (padHist T z) ∂(Measure.pi fun _ : Fin T => μ)
      ≤ ∫⁻ z, G (padHist N z) ∂(Measure.pi fun _ : Fin N => μ) := by
  rw [← pi_map_restrict μ T N h]
  refine le_trans (lintegral_map_le _ _) (le_of_eq (lintegral_congr fun z => ?_))
  refine hG _ _ fun r hr => ?_
  simp only [padHist, dif_pos hr, dif_pos (lt_of_lt_of_le hr h)]
  rfl

end blk

end OWMR.Asm

end Part6

section Part7

/-! Assembly, part 7: the explicit offset rule and its measurability. -/

open MeasureTheory
open scoped ENNReal NNReal


namespace OWMR.Asm

variable {n : ℕ} (N : Network n) (x : InitState n) (c : ConChoice n)

lemma cross_meas {β : Type} [MeasurableSpace β] (Qf θf pf nf : β → ℝ) (hQ : Measurable Qf)
    (hθ : Measurable θf) (hp : Measurable pf) (hn : Measurable nf) :
    MeasurableSet {ω | crossesThreshold (Qf ω) (θf ω) (pf ω) (nf ω)} := by
  have h1 : Measurable fun ω => 3 * Qf ω / 4 * θf ω := ((measurable_const.mul hQ).div_const _).mul hθ
  have h2 : Measurable fun ω => 3 * Qf ω / 4 * (1 + θf ω) :=
    ((measurable_const.mul hQ).div_const _).mul (measurable_const.add hθ)
  simp only [crossesThreshold, Set.setOf_or, Set.setOf_and]
  refine ((measurableSet_lt hp h1).inter (measurableSet_le h1 hn)).union
    (((measurableSet_lt hθ measurable_const).inter ((measurableSet_lt hp h2).inter
      (measurableSet_le h2 hn))).union ((measurableSet_lt hp hQ).inter (measurableSet_eq_fun hn hQ)))

lemma ship_meas {β : Type} [MeasurableSpace β] (Qf θf : β → ℝ) (Af : ℕ → β → ℝ)
    (hQ : Measurable Qf) (hθ : Measurable θf) (hA : ∀ k, Measurable (Af k)) :
    ∀ k, Measurable fun ω => shippedPath (Qf ω) (θf ω) (fun k => Af k ω) k
  | 0 => by
    simp only [shippedPath]
    exact Measurable.ite (cross_meas Qf θf (fun _ => 0) (Af 0) hQ hθ measurable_const (hA 0))
      (hA 0) measurable_const
  | k + 1 => by
    simp only [shippedPath]
    exact Measurable.ite (cross_meas Qf θf (Af k) (Af (k + 1)) hQ hθ (hA k) (hA (k + 1)))
      (hA (k + 1)) (ship_meas Qf θf Af hQ hθ hA k)

lemma ship_congr (Q θ' : ℝ) (A1 A2 : ℕ → ℝ) : ∀ k, (∀ k' ≤ k, A1 k' = A2 k') →
    shippedPath Q θ' A1 k = shippedPath Q θ' A2 k
  | 0, h => by simp only [shippedPath, h 0 le_rfl]
  | k + 1, h => by
    simp only [shippedPath, h k (by omega), h (k + 1) le_rfl,
      ship_congr Q θ' A1 A2 k (fun k' hk' => h k' (by omega))]

/-- The demand path with the block `b` spliced in from period `s`. -/
def splice (s : ℕ) (d : ℕ → DemandVec n) (b : Fin N.L0 → DemandVec n) : ℕ → DemandVec n :=
  fun r => if r < s then d r else padHist N.L0 b (r - s)

lemma splice_meas (s : ℕ) :
    Measurable fun p : (ℕ → DemandVec n) × (Fin N.L0 → DemandVec n) => splice N s p.1 p.2 := by
  refine measurable_pi_lambda _ fun r => ?_
  unfold splice
  by_cases hr : r < s
  · simp only [if_pos hr]; exact (measurable_pi_apply r).comp measurable_fst
  · simp only [if_neg hr]
    exact (measurable_pi_apply (r - s)).comp
      ((measurable_padHist' (α := DemandVec n) N.L0).comp measurable_snd)

/-- Depletion along the spliced path. -/
def XS (s : ℕ) (d : ℕ → DemandVec n) (b : Fin N.L0 → DemandVec n) (k : ℕ) : ℝ :=
  ∑ j, (c.S j - Ph N x c (splice N s d b) (s + k) j)

/-- The credited proxy along the spliced path. -/
def ZS (s : ℕ) (i : Fin n) (d : ℕ → DemandVec n) (θ' : ℝ) (b : Fin N.L0 → DemandVec n) : ℝ :=
  N.K i * Ncnt θ' + (N.h + N.p) * ∑ k ∈ Finset.range (N.L0 + 1),
    max (A N x c d s i (s + k) - shippedPath (q N x c d s i) θ' (fun k => A N x c d s i (s + k)) k
      - XS N x c s d b k) 0

/-- `z_j(ϑ)`, explicitly. -/
def zE (s : ℕ) (i : Fin n) (d : ℕ → DemandVec n) (θ' : ℝ) : ℝ≥0∞ :=
  ∫⁻ b, ENNReal.ofReal (ZS N x c s i d θ' b) ∂(Measure.pi fun _ : Fin N.L0 => N.μ)

/-- `z̄_j`, explicitly. -/
def zbarE (s : ℕ) (i : Fin n) (d : ℕ → DemandVec n) : ℝ≥0∞ :=
  ∫⁻ θ' in Set.Ioo (0 : ℝ) 1, zE N x c s i d θ'

/-- The ordinary request index. -/
abbrev jE (s : ℕ) (i : Fin n) (d : ℕ → DemandVec n) : ℕ :=
  ∑ r ∈ Finset.range s, (if 0 < r ∧ act N x c d (r - 1) then
      ((List.finRange n).filter (fun j => decide (0 < q N x c d r j))).length else 0)
    + ((List.finRange n).filter (fun j => decide (0 < q N x c d s j))).idxOf i + 1

open Classical in
/-- The deterministic offset rule, explicitly. -/
def thE (s : ℕ) (i : Fin n) (d : ℕ → DemandVec n) : ℝ :=
  if h : ∃ k : ℕ, zE N x c s i d ((c.enum k : ℚ) : ℝ)
      < zbarE N x c s i d + (2 : ℝ≥0∞)⁻¹ ^ jE N x c s i d then
    ((c.enum (Nat.find h) : ℚ) : ℝ)
  else 1 / 2

lemma meas_decide {β : Type} [MeasurableSpace β] (P : β → Prop) [DecidablePred P]
    (h : MeasurableSet {x | P x}) : Measurable fun x => decide (P x) := by
  refine measurable_to_countable' fun b => ?_
  cases b
  · have : (fun x => decide (P x)) ⁻¹' {false} = {x | P x}ᶜ := by ext x; simp
    rw [this]; exact h.compl
  · have : (fun x => decide (P x)) ⁻¹' {true} = {x | P x} := by ext x; simp
    rw [this]; exact h

lemma Ncnt_meas : Measurable Ncnt := by
  unfold Ncnt
  exact measurable_const.add (Measurable.ite (measurableSet_lt measurable_id measurable_const)
    measurable_const measurable_const)

lemma ZS_meas (s : ℕ) (i : Fin n) :
    Measurable fun p : ((ℕ → DemandVec n) × ℝ) × (Fin N.L0 → DemandVec n) =>
      ZS N x c s i p.1.1 p.1.2 p.2 := by
  unfold ZS XS
  have hA : ∀ k, Measurable fun p : ((ℕ → DemandVec n) × ℝ) × (Fin N.L0 → DemandVec n) =>
      A N x c p.1.1 s i (s + k) := fun k => (A_meas N x c s i (s + k)).comp
    (measurable_fst.comp measurable_fst)
  have hsp : Measurable fun p : ((ℕ → DemandVec n) × ℝ) × (Fin N.L0 → DemandVec n) =>
      splice N s p.1.1 p.2 :=
    (splice_meas N s).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  refine (measurable_const.mul (Ncnt_meas.comp (measurable_snd.comp measurable_fst))).add
    (measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_))
  refine Measurable.max (((hA k).sub ?_).sub ?_) measurable_const
  · exact ship_meas (fun p : ((ℕ → DemandVec n) × ℝ) × (Fin N.L0 → DemandVec n) =>
      q N x c p.1.1 s i) (fun p => p.1.2) (fun k p => A N x c p.1.1 s i (s + k))
      ((q_meas N x c s i).comp (measurable_fst.comp measurable_fst))
      (measurable_snd.comp measurable_fst) hA k
  · exact Finset.measurable_sum _ fun j _ => measurable_const.sub
      ((Ph_meas N x c (s + k) j).comp hsp)

lemma zE_meas (s : ℕ) (i : Fin n) :
    Measurable fun p : (ℕ → DemandVec n) × ℝ => zE N x c s i p.1 p.2 := by
  unfold zE
  exact Measurable.lintegral_prod_right' (f := fun p : ((ℕ → DemandVec n) × ℝ) ×
    (Fin N.L0 → DemandVec n) => ENNReal.ofReal (ZS N x c s i p.1.1 p.1.2 p.2))
    (ZS_meas N x c s i).ennreal_ofReal

lemma zbarE_meas (s : ℕ) (i : Fin n) : Measurable fun d => zbarE N x c s i d := by
  unfold zbarE
  exact Measurable.lintegral_prod_right' (f := fun p : (ℕ → DemandVec n) × ℝ =>
    zE N x c s i p.1 p.2) (zE_meas N x c s i)

lemma qpos_meas (r : ℕ) : Measurable fun d : ℕ → DemandVec n =>
    fun j : Fin n => decide (0 < q N x c d r j) :=
  measurable_pi_lambda _ fun j => meas_decide _ (measurableSet_lt measurable_const
    (q_meas N x c r j))

lemma jE_meas (s : ℕ) (i : Fin n) : Measurable fun d => jE N x c s i d := by
  unfold jE
  have h1 : Measurable fun d : ℕ → DemandVec n => ∑ r ∈ Finset.range s,
      (if 0 < r ∧ act N x c d (r - 1) then
        ((List.finRange n).filter (fun j => decide (0 < q N x c d r j))).length else 0) := by
    refine Finset.measurable_sum _ fun r _ => ?_
    refine Measurable.ite ((MeasurableSet.const _).inter (act_meas N x c (r - 1))) ?_
      measurable_const
    exact (measurable_of_countable (fun v : Fin n → Bool =>
      ((List.finRange n).filter (fun j => v j)).length)).comp (qpos_meas N x c r)
  have h2 : Measurable fun d : ℕ → DemandVec n =>
      ((List.finRange n).filter (fun j => decide (0 < q N x c d s j))).idxOf i :=
    (measurable_of_countable (fun v : Fin n → Bool =>
      ((List.finRange n).filter (fun j => v j)).idxOf i)).comp (qpos_meas N x c s)
  exact (h1.add h2).add measurable_const

lemma thE_meas (s : ℕ) (i : Fin n) : Measurable fun d => thE N x c s i d := by
  classical
  set P : (ℕ → DemandVec n) → ℕ → Prop := fun d k => zE N x c s i d ((c.enum k : ℚ) : ℝ)
      < zbarE N x c s i d + (2 : ℝ≥0∞)⁻¹ ^ jE N x c s i d with hP
  have hPm : ∀ k, MeasurableSet {d | P d k} := fun k => by
    have h1 : Measurable fun d => zE N x c s i d ((c.enum k : ℚ) : ℝ) :=
      (zE_meas N x c s i).comp (measurable_id.prodMk measurable_const)
    have h2 : Measurable fun d => (2 : ℝ≥0∞)⁻¹ ^ jE N x c s i d :=
      (measurable_of_countable (fun m : ℕ => (2 : ℝ≥0∞)⁻¹ ^ m)).comp (jE_meas N x c s i)
    exact measurableSet_lt h1 ((zbarE_meas N x c s i).add h2)
  set κ : (ℕ → DemandVec n) → ℕ := fun d =>
    if h : ∃ k, P d k then Nat.find h + 1 else 0 with hκ
  have hκm : Measurable κ := by
    refine measurable_to_countable' fun o => ?_
    cases o with
    | zero =>
      have : κ ⁻¹' {0} = ⋂ k, {d | P d k}ᶜ := by
        ext d
        simp only [Set.mem_preimage, Set.mem_singleton_iff, hκ, Set.mem_iInter, Set.mem_compl_iff,
          Set.mem_setOf_eq]
        constructor
        · intro h k hk
          rw [dif_pos ⟨k, hk⟩] at h
          omega
        · intro h
          rw [dif_neg (fun ⟨k, hk⟩ => h k hk)]
      rw [this]; exact MeasurableSet.iInter fun k => (hPm k).compl
    | succ k =>
      have : κ ⁻¹' {k + 1} = {d | P d k} ∩ ⋂ k' ∈ Finset.range k, {d | P d k'}ᶜ := by
        ext d
        simp only [Set.mem_preimage, Set.mem_singleton_iff, hκ, Set.mem_inter_iff,
          Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range, Set.mem_compl_iff]
        constructor
        · intro h
          by_cases hex : ∃ k, P d k
          · rw [dif_pos hex] at h
            have hk : Nat.find hex = k := by omega
            subst hk
            exact ⟨Nat.find_spec hex, fun k' hk' => Nat.find_min hex hk'⟩
          · rw [dif_neg hex] at h; omega
        · rintro ⟨h1, h2⟩
          have hex : ∃ k, P d k := ⟨k, h1⟩
          rw [dif_pos hex]
          have := le_antisymm (Nat.find_min' hex h1) (not_lt.1 fun hlt => h2 _ hlt (Nat.find_spec hex))
          omega
      rw [this]
      exact (hPm k).inter (MeasurableSet.biInter (Set.to_countable _) fun k' _ => (hPm k').compl)
  have heq : (fun d => thE N x c s i d) = (fun o : ℕ => match o with
      | k + 1 => ((c.enum k : ℚ) : ℝ)
      | 0 => 1 / 2) ∘ κ := by
    funext d
    simp only [Function.comp, hκ, thE]
    by_cases hex : ∃ k, P d k
    · rw [dif_pos hex, dif_pos hex]
    · rw [dif_neg hex, dif_neg hex]
  rw [heq]
  exact (measurable_of_countable _).comp hκm

section ident7

variable (θ : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)
  (hident : ∀ d s i, 0 < s → act N x c d (s - 1) → 0 < q N x c d s i → c.batch i = true →
        ∃ σ : EngState n,
          θ d s i = conRule N c σ s (∑ r ∈ Finset.range s,
              (if 0 < r ∧ act N x c d (r - 1) then
                ((List.finRange n).filter (fun j => decide (0 < q N x c d r j))).length else 0)
            + ((List.finRange n).filter (fun j => decide (0 < q N x c d s j))).idxOf i + 1) i
              (q N x c d s i) ∧
          ∀ (ds : Fin N.L0 → DemandVec n) (k : ℕ), k ≤ N.L0 →
            idealAlloc N c.params σ s i (q N x c d s i) (padHist N.L0 ds) k = A N x c d s i (s + k) ∧
            idealDepletion N c.params σ s (padHist N.L0 ds) k
              = ∑ j, (c.S j - Ph N x c (fun r => if r < s then d r else padHist N.L0 ds (r - s))
                  (s + k) j))

include hident in
/-- On ordinary requests of batch retailers the offsets are given by the explicit rule. -/
lemma theta_eq (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) (ho : ord N x c d s i) :
    θ d s i = thE N x c s i d := by
  obtain ⟨hs, ha, hq, hb⟩ := ho
  obtain ⟨σ, h1, h2⟩ := hident d s i hs ha hq hb
  rw [h1]
  have hpm : ∀ θ', proxyMean N c.params σ s i (q N x c d s i) θ' = zE N x c s i d θ' := by
    intro θ'
    unfold proxyMean zE
    refine lintegral_congr fun ds => ?_
    congr 1
    unfold proxy ZS Ncnt XS splice
    congr 2
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ N.L0 := by simp at hk; omega
    obtain ⟨e1, e2⟩ := h2 ds k hk'
    rw [e1, e2, ship_congr _ _ _ _ k (fun k' hk'' => (h2 ds k' (by omega)).1)]
  have hbar : (∫⁻ θ' in Set.Ioo (0 : ℝ) 1, proxyMean N c.params σ s i (q N x c d s i) θ')
      = zbarE N x c s i d := by
    unfold zbarE; exact lintegral_congr fun θ' => hpm θ'
  have key : ∀ k, (proxyMean N c.params σ s i (q N x c d s i) ((c.enum k : ℚ) : ℝ)
      < (∫⁻ θ' in Set.Ioo (0 : ℝ) 1, proxyMean N c.params σ s i (q N x c d s i) θ')
        + (2 : ℝ≥0∞)⁻¹ ^ jE N x c s i d)
      ↔ (zE N x c s i d ((c.enum k : ℚ) : ℝ) < zbarE N x c s i d + (2 : ℝ≥0∞)⁻¹ ^ jE N x c s i d) :=
    fun k => by rw [hpm, hbar]
  have hj : (∑ r ∈ Finset.range s, (if 0 < r ∧ act N x c d (r - 1) then
        ((List.finRange n).filter (fun j => decide (0 < q N x c d r j))).length else 0)
      + ((List.finRange n).filter (fun j => decide (0 < q N x c d s j))).idxOf i + 1)
      = jE N x c s i d := rfl
  unfold conRule thE
  simp only
  by_cases hex : ∃ k, zE N x c s i d ((c.enum k : ℚ) : ℝ)
      < zbarE N x c s i d + (2 : ℝ≥0∞)⁻¹ ^ jE N x c s i d
  · have hex' : ∃ k, proxyMean N c.params σ s i (q N x c d s i) ((c.enum k : ℚ) : ℝ)
        < (∫⁻ θ' in Set.Ioo (0 : ℝ) 1, proxyMean N c.params σ s i (q N x c d s i) θ')
          + (2 : ℝ≥0∞)⁻¹ ^ jE N x c s i d := by
      obtain ⟨k, hk⟩ := hex; exact ⟨k, (key k).2 hk⟩
    rw [dif_pos hex', dif_pos hex]
    have : Nat.find hex' = Nat.find hex := le_antisymm
      (Nat.find_min' hex' ((key _).2 (Nat.find_spec hex)))
      (Nat.find_min' hex ((key _).1 (Nat.find_spec hex')))
    rw [this]
  · have hex' : ¬ ∃ k, proxyMean N c.params σ s i (q N x c d s i) ((c.enum k : ℚ) : ℝ)
        < (∫⁻ θ' in Set.Ioo (0 : ℝ) 1, proxyMean N c.params σ s i (q N x c d s i) θ')
          + (2 : ℝ≥0∞)⁻¹ ^ jE N x c s i d := fun ⟨k, hk⟩ => hex ⟨k, (key k).1 hk⟩
    rw [dif_neg hex', dif_neg hex]

end ident7

end OWMR.Asm

end Part7

section Part8

/-! Assembly, part 8: past dependence of the explicit rule and the derandomization step. -/

open MeasureTheory
open scoped ENNReal NNReal


namespace OWMR.Asm

variable {n : ℕ} (N : Network n) (x : InitState n) (c : ConChoice n)

lemma A_dep2 (s : ℕ) (i : Fin n) (t : ℕ) (d d' : ℕ → DemandVec n)
    (h : ∀ r < s, d r = d' r) (ht : t + 1 - N.L0 ≤ s + 1) :
    A N x c d s i t = A N x c d' s i t := by
  rw [A_eq, A_eq]
  have hq : ∀ r ≤ s, ∀ j, q N x c d r j = q N x c d' r j := fun r hr j =>
    q_dep N x c r d d' (fun r' hr' => h r' (by omega)) j
  have hV : V N x c d t = V N x c d' t := by
    unfold V
    exact Finset.sum_congr rfl fun r hr => q0_dep N x c r d d'
      (fun r' hr' => h r' (by simp at hr; omega))
  have hah : ahead N x c d s i = ahead N x c d' s i := by
    unfold ahead
    rw [Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun j _ =>
      hq r (by simp at hr; omega) j]
    rw [Finset.sum_congr rfl fun j _ => hq s le_rfl j]
  rw [hq s le_rfl i, hV, hah]

lemma splice_dep (s : ℕ) (d d' : ℕ → DemandVec n) (b : Fin N.L0 → DemandVec n)
    (h : ∀ r < s, d r = d' r) : splice N s d b = splice N s d' b := by
  funext r; unfold splice; split_ifs with hr
  · exact h r hr
  · rfl

lemma XS_dep (s : ℕ) (d d' : ℕ → DemandVec n) (b : Fin N.L0 → DemandVec n) (k : ℕ)
    (h : ∀ r < s, d r = d' r) : XS N x c s d b k = XS N x c s d' b k := by
  unfold XS; rw [splice_dep N s d d' b h]

lemma ZS_dep (s : ℕ) (i : Fin n) (d d' : ℕ → DemandVec n) (θ' : ℝ) (b : Fin N.L0 → DemandVec n)
    (h : ∀ r < s, d r = d' r) : ZS N x c s i d θ' b = ZS N x c s i d' θ' b := by
  unfold ZS
  congr 2
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ N.L0 := by simp at hk; omega
  have hA : ∀ k' ≤ k, A N x c d s i (s + k') = A N x c d' s i (s + k') := fun k' hk'' =>
    A_dep2 N x c s i (s + k') d d' h (by omega)
  rw [hA k le_rfl, q_dep N x c s d d' h i,
    ship_congr _ _ _ (fun k => A N x c d' s i (s + k)) k hA, XS_dep N x c s d d' b k h]

lemma zE_dep (s : ℕ) (i : Fin n) (d d' : ℕ → DemandVec n) (θ' : ℝ) (h : ∀ r < s, d r = d' r) :
    zE N x c s i d θ' = zE N x c s i d' θ' := by
  unfold zE; exact lintegral_congr fun b => by rw [ZS_dep N x c s i d d' θ' b h]

lemma zbarE_dep (s : ℕ) (i : Fin n) (d d' : ℕ → DemandVec n) (h : ∀ r < s, d r = d' r) :
    zbarE N x c s i d = zbarE N x c s i d' := by
  unfold zbarE; exact lintegral_congr fun θ' => zE_dep N x c s i d d' θ' h

lemma jE_dep (s : ℕ) (i : Fin n) (d d' : ℕ → DemandVec n) (h : ∀ r < s, d r = d' r) :
    jE N x c s i d = jE N x c s i d' := by
  have hq : ∀ r ≤ s, ∀ j, q N x c d r j = q N x c d' r j := fun r hr j =>
    q_dep N x c r d d' (fun r' hr' => h r' (by omega)) j
  unfold jE
  congr 2
  · refine Finset.sum_congr rfl fun r hr => ?_
    have hr' : r < s := Finset.mem_range.1 hr
    have ha := act_dep N x c (r - 1) d d' (fun r' hr'' => h r' (by omega))
    simp only [hq r hr'.le, ha]
  · simp only [hq s le_rfl]

lemma thE_dep (s : ℕ) (i : Fin n) (d d' : ℕ → DemandVec n) (h : ∀ r < s, d r = d' r) :
    thE N x c s i d = thE N x c s i d' := by
  have h1 : ∀ θ', zE N x c s i d θ' = zE N x c s i d' θ' := fun θ' => zE_dep N x c s i d d' θ' h
  have h2 := zbarE_dep N x c s i d d' h
  have h3 := jE_dep N x c s i d d' h
  have key : ∀ k, (zE N x c s i d ((c.enum k : ℚ) : ℝ) < zbarE N x c s i d
        + (2 : ℝ≥0∞)⁻¹ ^ jE N x c s i d)
      ↔ (zE N x c s i d' ((c.enum k : ℚ) : ℝ) < zbarE N x c s i d'
        + (2 : ℝ≥0∞)⁻¹ ^ jE N x c s i d') := fun k => by rw [h1, h2, h3]
  unfold thE
  by_cases hex : ∃ k, zE N x c s i d ((c.enum k : ℚ) : ℝ) < zbarE N x c s i d
      + (2 : ℝ≥0∞)⁻¹ ^ jE N x c s i d
  · have hex' : ∃ k, zE N x c s i d' ((c.enum k : ℚ) : ℝ) < zbarE N x c s i d'
        + (2 : ℝ≥0∞)⁻¹ ^ jE N x c s i d' := by
      obtain ⟨k, hk⟩ := hex; exact ⟨k, (key k).1 hk⟩
    rw [dif_pos hex, dif_pos hex']
    have : Nat.find hex = Nat.find hex' := le_antisymm
      (Nat.find_min' hex ((key _).2 (Nat.find_spec hex')))
      (Nat.find_min' hex' ((key _).1 (Nat.find_spec hex)))
    rw [this]
  · have hex' : ¬ ∃ k, zE N x c s i d' ((c.enum k : ℚ) : ℝ) < zbarE N x c s i d'
        + (2 : ℝ≥0∞)⁻¹ ^ jE N x c s i d' := fun ⟨k, hk⟩ => hex ⟨k, (key k).2 hk⟩
    rw [dif_neg hex, dif_neg hex']

lemma ord_dep (s : ℕ) (i : Fin n) (d d' : ℕ → DemandVec n) (h : ∀ r < s, d r = d' r) :
    ord N x c d s i ↔ ord N x c d' s i := by
  unfold ord
  rw [act_dep N x c (s - 1) d d' (fun r hr => h r (by omega)), q_dep N x c s d d' h i]

lemma ord_meas (s : ℕ) (i : Fin n) : MeasurableSet {d : ℕ → DemandVec n | ord N x c d s i} := by
  unfold ord
  have : {d : ℕ → DemandVec n | 0 < s ∧ act N x c d (s - 1) ∧ 0 < q N x c d s i ∧ c.batch i = true}
      = {_d | 0 < s} ∩ ({d | act N x c d (s - 1)} ∩ ({d | 0 < q N x c d s i} ∩ {_d | c.batch i = true})) := by
    ext d; simp
  rw [this]
  exact (MeasurableSet.const _).inter ((act_meas N x c _).inter
    ((measurableSet_lt measurable_const (q_meas N x c s i)).inter (MeasurableSet.const _)))

/-- The proxy along the actual path is the spliced proxy at the actual block. -/
lemma Zexp_eq_ZS (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) (θ' : ℝ) :
    Zexp N x c d s i θ' = ZS N x c s i d θ' (fun j => d (s + j)) := by
  unfold Zexp ZS
  congr 2
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ N.L0 := by simp at hk; omega
  congr 2
  unfold XS X
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Ph_dep N x c (s + k) _ _ (fun r hr => ?_) j
  unfold splice
  split_ifs with h1
  · rfl
  · have : r - s < N.L0 := by omega
    simp only [padHist, dif_pos this]
    congr 1; omega

/-- The credited bound of an ordinary request along the actual path. -/
def Bx (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) : ℝ :=
  7 / 3 * N.K i + (N.h + N.p) * ∑ k ∈ Finset.range (N.L0 + 1),
    (if 0 < A N x c d s i (s + k) ∧ A N x c d s i (s + k) < q N x c d s i then
      crA N x c d s i (s + k) else 0)

/-- The credited bound along the spliced path. -/
def BS (s : ℕ) (i : Fin n) (d : ℕ → DemandVec n) (b : Fin N.L0 → DemandVec n) : ℝ :=
  7 / 3 * N.K i + (N.h + N.p) * ∑ k ∈ Finset.range (N.L0 + 1),
    (if 0 < A N x c d s i (s + k) ∧ A N x c d s i (s + k) < q N x c d s i then
      max (3 * q N x c d s i / 4 - XS N x c s d b k) 0 ^ 2 / (3 * q N x c d s i / 2) else 0)

lemma XS_block (d : ℕ → DemandVec n) (s : ℕ) (k : ℕ) (hk : k ≤ N.L0) :
    XS N x c s d (fun j => d (s + j)) k = X N x c d (s + k) := by
  unfold XS X
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Ph_dep N x c (s + k) _ _ (fun r hr => ?_) j
  unfold splice
  split_ifs with h1
  · rfl
  · have : r - s < N.L0 := by omega
    simp only [padHist, dif_pos this]
    congr 1; omega

lemma BS_block (d : ℕ → DemandVec n) (s : ℕ) (i : Fin n) :
    BS N x c s i d (fun j => d (s + j)) = Bx N x c d s i := by
  unfold BS Bx crA
  congr 2
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [XS_block N x c d s k (by simp at hk; omega)]

lemma XS_nonneg (hsS : ∀ i, c.s i ≤ c.S i) (s : ℕ) (d : ℕ → DemandVec n)
    (b : Fin N.L0 → DemandVec n) (k : ℕ) : 0 ≤ XS N x c s d b k :=
  Finset.sum_nonneg fun j _ => sub_nonneg.2 (Ph_bounds N x c hsS _ _ j).2

lemma XS_meas_b (s : ℕ) (d : ℕ → DemandVec n) (k : ℕ) :
    Measurable fun b : Fin N.L0 → DemandVec n => XS N x c s d b k :=
  Finset.measurable_sum _ fun j _ => measurable_const.sub
    ((Ph_meas N x c (s + k) j).comp ((splice_meas N s).comp (measurable_const.prodMk measurable_id)))

lemma BS_meas (s : ℕ) (i : Fin n) :
    Measurable fun p : (ℕ → DemandVec n) × (Fin N.L0 → DemandVec n) => BS N x c s i p.1 p.2 := by
  unfold BS XS
  refine measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_))
  refine Measurable.ite ?_ ?_ measurable_const
  · exact ((measurableSet_lt measurable_const ((A_meas N x c s i (s + k)).comp measurable_fst)).inter
      (measurableSet_lt ((A_meas N x c s i (s + k)).comp measurable_fst)
        ((q_meas N x c s i).comp measurable_fst)))
  · refine Measurable.div (Measurable.pow_const (Measurable.max (Measurable.sub ?_
      (Finset.measurable_sum _ fun j _ => measurable_const.sub ((Ph_meas N x c (s + k) j).comp
        (splice_meas N s)))) measurable_const) _) ?_
    · exact ((measurable_const.mul ((q_meas N x c s i).comp measurable_fst)).div_const _)
    · exact ((measurable_const.mul ((q_meas N x c s i).comp measurable_fst)).div_const _)

/-- Averaging the proxy over the offset is at most the credited bound (Lemma C.3). -/
lemma avg_le_BS (hN : N.Standing) (hsS : ∀ i, c.s i ≤ c.S i) (hs0S : c.s0 ≤ c.S0)
    (s : ℕ) (i : Fin n) (d : ℕ → DemandVec n) (hq : 0 < q N x c d s i)
    (b : Fin N.L0 → DemandVec n) :
    ∫⁻ θ' in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (ZS N x c s i d θ' b)
      ≤ ENNReal.ofReal (BS N x c s i d b) := by
  have hh := hN.h_pos.le; have hp := hN.p_pos.le
  have hK := hN.K_nonneg i
  set Q := q N x c d s i with hQ
  set A' : ℕ → ℝ := fun k => A N x c d s i (s + k) with hA'
  obtain ⟨c1, c2, -, c4, c5⟩ := arb_credited_reserve Q A' hq (A_nonneg N x c d s i _)
    (fun k k' hk => A_mono N x c hs0S d s i (by omega)) (fun k => A_le_q N x c hsS d s i _)
  set z : ℕ → ℝ := fun k => XS N x c s d b k with hz
  have hz0 : ∀ k, 0 ≤ z k := fun k => XS_nonneg N x c hsS s d b k
  have hmk : ∀ k, Measurable fun θ' : ℝ => ENNReal.ofReal ((N.h + N.p)
      * max (A' k - shippedPath Q θ' A' k - z k) 0) := fun k =>
    (measurable_const.mul ((measurable_const.sub (ship_meas (fun _ : ℝ => Q) id (fun k _ => A' k)
      measurable_const measurable_id (fun _ => measurable_const) k)).sub measurable_const
        |>.max measurable_const)).ennreal_ofReal
  have hNm : Measurable fun θ' : ℝ => ENNReal.ofReal (N.K i * Ncnt θ') :=
    (measurable_const.mul Ncnt_meas).ennreal_ofReal
  have e1 : ∀ θ', ENNReal.ofReal (ZS N x c s i d θ' b)
      = ENNReal.ofReal (N.K i * Ncnt θ') + ∑ k ∈ Finset.range (N.L0 + 1),
          ENNReal.ofReal ((N.h + N.p) * max (A' k - shippedPath Q θ' A' k - z k) 0) := fun θ' => by
    unfold ZS
    rw [ENNReal.ofReal_add (mul_nonneg hK (Ncnt_nonneg θ'))
      (mul_nonneg (by linarith) (Finset.sum_nonneg fun k _ => le_max_right _ _)), Finset.mul_sum,
      ENNReal.ofReal_sum_of_nonneg fun k _ => mul_nonneg (by linarith) (le_max_right _ _)]
  simp_rw [e1]
  rw [lintegral_add_left hNm, lintegral_finsetSum _ fun k _ => hmk k]
  have hset : ∫⁻ θ' in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (N.K i * Ncnt θ')
      = ENNReal.ofReal (7 / 3 * N.K i) := by
    have : ∀ θ', ENNReal.ofReal (N.K i * Ncnt θ') = ENNReal.ofReal (N.K i)
        * ENNReal.ofReal (1 + if θ' < 1 / 3 then 2 else 1) := fun θ' => by
      rw [← ENNReal.ofReal_mul hK]; rfl
    simp_rw [this]
    rw [lintegral_const_mul (ENNReal.ofReal (N.K i))
      (f := fun θ' : ℝ => ENNReal.ofReal (1 + if θ' < 1 / 3 then 2 else 1))
      Ncnt_meas.ennreal_ofReal, c5, ← ENNReal.ofReal_mul hK]
    ring_nf
  have hk : ∀ k ∈ Finset.range (N.L0 + 1),
      ∫⁻ θ' in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((N.h + N.p)
        * max (A' k - shippedPath Q θ' A' k - z k) 0)
      ≤ ENNReal.ofReal ((N.h + N.p) * (if 0 < A' k ∧ A' k < Q then
          max (3 * Q / 4 - z k) 0 ^ 2 / (3 * Q / 2) else 0)) := by
    intro k _
    have e2 : ∀ θ', ENNReal.ofReal ((N.h + N.p) * max (A' k - shippedPath Q θ' A' k - z k) 0)
        = ENNReal.ofReal (N.h + N.p) * ENNReal.ofReal (A' k - shippedPath Q θ' A' k - z k) :=
      fun θ' => by
        rw [ENNReal.ofReal_mul (by linarith)]
        congr 1
        rcases le_total (A' k - shippedPath Q θ' A' k - z k) 0 with h1 | h1
        · rw [max_eq_right h1, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h1]
        · rw [max_eq_left h1]
    simp_rw [e2]
    have hm' : Measurable fun θ' : ℝ => ENNReal.ofReal (A' k - shippedPath Q θ' A' k - z k) :=
      ((measurable_const.sub (ship_meas (fun _ : ℝ => Q) id (fun k _ => A' k)
        measurable_const measurable_id (fun _ => measurable_const) k)).sub measurable_const).ennreal_ofReal
    rw [lintegral_const_mul _ hm', ENNReal.ofReal_mul (by linarith)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    by_cases hc : 0 < A' k ∧ A' k < Q
    · rw [if_pos hc]; exact c4 k (z k) (hz0 k) hc.2
    · rw [if_neg hc, ENNReal.ofReal_zero]
      have hzero : ∀ θ', ENNReal.ofReal (A' k - shippedPath Q θ' A' k - z k) = 0 := by
        intro θ'
        apply ENNReal.ofReal_of_nonpos
        rcases not_and_or.1 hc with h | h
        · have h0 : A' k = 0 := le_antisymm (not_lt.1 h) (A_nonneg N x c d s i _)
          have := (c1 θ' k).1
          linarith [(c1 θ' k).2, hz0 k]
        · have hQk : A' k = Q := le_antisymm (A_le_q N x c hsS d s i _) (not_lt.1 h)
          rw [c2 θ' k hQk, hQk]; linarith [hz0 k]
      simp [hzero]
  rw [hset]
  calc ENNReal.ofReal (7 / 3 * N.K i) + ∑ k ∈ Finset.range (N.L0 + 1),
        ∫⁻ θ' in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((N.h + N.p)
          * max (A' k - shippedPath Q θ' A' k - z k) 0)
      ≤ ENNReal.ofReal (7 / 3 * N.K i) + ∑ k ∈ Finset.range (N.L0 + 1),
        ENNReal.ofReal ((N.h + N.p) * (if 0 < A' k ∧ A' k < Q then
          max (3 * Q / 4 - z k) 0 ^ 2 / (3 * Q / 2) else 0)) := by
        gcongr with k hk'; exact hk k hk'
    _ = ENNReal.ofReal (BS N x c s i d b) := by
        unfold BS
        have hnn : ∀ k ∈ Finset.range (N.L0 + 1), 0 ≤ (N.h + N.p) * (if 0 < A' k ∧ A' k < Q then
            max (3 * Q / 4 - z k) 0 ^ 2 / (3 * Q / 2) else 0) := fun k _ => by
          refine mul_nonneg (by linarith) ?_
          split_ifs
          · positivity
          · exact le_rfl
        rw [ENNReal.ofReal_add (by positivity) (by rw [Finset.mul_sum]; exact Finset.sum_nonneg hnn),
          Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg hnn]

/-- The selected offset keeps the conditional proxy below its average plus `2^{-j}`. -/
lemma zE_thE_lt (hN : N.Standing) (hsS : ∀ i, c.s i ≤ c.S i) (s : ℕ) (i : Fin n)
    (d : ℕ → DemandVec n) (hq : 0 < q N x c d s i) :
    zE N x c s i d (thE N x c s i d) < zbarE N x c s i d + (2 : ℝ≥0∞)⁻¹ ^ jE N x c s i d := by
  have hh := hN.h_pos.le; have hp := hN.p_pos.le
  obtain ⟨k, hk⟩ := con_offset_exists (Measure.pi fun _ : Fin N.L0 => N.μ) (N.K i) (N.h + N.p)
    (q N x c d s i) (hN.K_nonneg i) (by linarith) hq (fun k => A N x c d s i (s + k))
    (fun k => A_nonneg N x c d s i _) (fun k => A_le_q N x c hsS d s i _) N.L0
    (fun b k => XS N x c s d b k) (fun k => XS_meas_b N x c s d k)
    (fun b k => XS_nonneg N x c hsS s d b k) c.enum (jE N x c s i d)
  have hex : ∃ k : ℕ, zE N x c s i d ((c.enum k : ℚ) : ℝ)
      < zbarE N x c s i d + (2 : ℝ≥0∞)⁻¹ ^ jE N x c s i d := ⟨k, hk⟩
  have e : thE N x c s i d = ((c.enum (Nat.find hex) : ℚ) : ℝ) := by
    unfold thE; rw [dif_pos hex]
  rw [e]
  exact Nat.find_spec hex

/-- The derandomization step for one request slot (tower property and Lemma C.7). -/
lemma derand (hN : N.Standing) (hsS : ∀ i, c.s i ≤ c.S i) (hs0S : c.s0 ≤ c.S0) (N' s : ℕ)
    (i : Fin n) (hsN : s + N.L0 ≤ N') :
    ∫⁻ z, (if ord N x c (padHist N' z) s i then
        ENNReal.ofReal (Zexp N x c (padHist N' z) s i (thE N x c s i (padHist N' z))) else 0)
        ∂(Measure.pi fun _ : Fin N' => N.μ)
      ≤ ∫⁻ z, (if ord N x c (padHist N' z) s i then
          ENNReal.ofReal (Bx N x c (padHist N' z) s i) else 0) ∂(Measure.pi fun _ : Fin N' => N.μ)
        + ∫⁻ z, (if ord N x c (padHist N' z) s i then
          (2 : ℝ≥0∞)⁻¹ ^ jE N x c s i (padHist N' z) else 0) ∂(Measure.pi fun _ : Fin N' => N.μ) := by
  have hD := measurable_padHist' (α := DemandVec n) N'
  set Φ : (ℕ → DemandVec n) → (Fin N.L0 → DemandVec n) → ℝ≥0∞ := fun d b =>
    if ord N x c d s i then ENNReal.ofReal (ZS N x c s i d (thE N x c s i d) b) else 0 with hΦ
  have hom : MeasurableSet {p : (ℕ → DemandVec n) × (Fin N.L0 → DemandVec n) | ord N x c p.1 s i} :=
    measurable_fst (ord_meas N x c s i)
  have hΦm : Measurable fun p : (ℕ → DemandVec n) × (Fin N.L0 → DemandVec n) => Φ p.1 p.2 :=
    Measurable.ite hom ((ZS_meas N x c s i).comp ((measurable_fst.prodMk
      ((thE_meas N x c s i).comp measurable_fst)).prodMk measurable_snd)).ennreal_ofReal
      measurable_const
  have hΦd : ∀ (d d' : ℕ → DemandVec n) (b : Fin N.L0 → DemandVec n), (∀ r < s, d r = d' r) →
      Φ d b = Φ d' b := by
    intro d d' b h
    simp only [hΦ]
    rw [thE_dep N x c s i d d' h, ZS_dep N x c s i d d' _ b h]
    by_cases ho : ord N x c d s i
    · rw [if_pos ho, if_pos ((ord_dep N x c s i d d' h).1 ho)]
    · rw [if_neg ho, if_neg (fun h' => ho ((ord_dep N x c s i d d' h).2 h'))]
  have e0 : ∀ z : Fin N' → DemandVec n, (if ord N x c (padHist N' z) s i then
      ENNReal.ofReal (Zexp N x c (padHist N' z) s i (thE N x c s i (padHist N' z))) else 0)
      = Φ (padHist N' z) (fun j => padHist N' z (s + j)) := fun z => by
    simp only [hΦ]; rw [Zexp_eq_ZS]
  rw [lintegral_congr e0, lintegral_blk N.μ N' s N.L0 hsN Φ hΦm hΦd]
  -- the conditional proxy
  set Ψ : (ℕ → DemandVec n) → ℝ≥0∞ := fun d =>
    if ord N x c d s i then zbarE N x c s i d else 0 with hΨ
  set Ξ : (ℕ → DemandVec n) → ℝ≥0∞ := fun d =>
    if ord N x c d s i then (2 : ℝ≥0∞)⁻¹ ^ jE N x c s i d else 0 with hΞ
  have hpt : ∀ d : ℕ → DemandVec n, ∫⁻ b, Φ d b ∂(Measure.pi fun _ : Fin N.L0 => N.μ)
      ≤ Ψ d + Ξ d := by
    intro d
    simp only [hΦ, hΨ, hΞ]
    by_cases ho : ord N x c d s i
    · simp only [if_pos ho]
      exact (zE_thE_lt N x c hN hsS s i d ho.2.2.1).le
    · simp [if_neg ho]
  have hΨm : Measurable fun z : Fin N' → DemandVec n => Ψ (padHist N' z) :=
    (Measurable.ite (ord_meas N x c s i) (zbarE_meas N x c s i) measurable_const).comp hD
  calc ∫⁻ z, ∫⁻ b, Φ (padHist N' z) b ∂(Measure.pi fun _ : Fin N.L0 => N.μ)
        ∂(Measure.pi fun _ : Fin N' => N.μ)
      ≤ ∫⁻ z, (Ψ (padHist N' z) + Ξ (padHist N' z)) ∂(Measure.pi fun _ : Fin N' => N.μ) :=
        lintegral_mono fun z => hpt _
    _ = ∫⁻ z, Ψ (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ)
        + ∫⁻ z, Ξ (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ) := lintegral_add_left hΨm _
    _ ≤ _ := by
        refine add_le_add ?_ le_rfl
        -- average over the offset, then return the block
        set Φ' : (ℕ → DemandVec n) → (Fin N.L0 → DemandVec n) → ℝ≥0∞ := fun d b =>
          if ord N x c d s i then ENNReal.ofReal (BS N x c s i d b) else 0 with hΦ'
        have hΦ'm : Measurable fun p : (ℕ → DemandVec n) × (Fin N.L0 → DemandVec n) => Φ' p.1 p.2 :=
          Measurable.ite hom (BS_meas N x c s i).ennreal_ofReal measurable_const
        have hΦ'd : ∀ (d d' : ℕ → DemandVec n) (b : Fin N.L0 → DemandVec n),
            (∀ r < s, d r = d' r) → Φ' d b = Φ' d' b := by
          intro d d' b h
          simp only [hΦ']
          have hBS : BS N x c s i d b = BS N x c s i d' b := by
            unfold BS
            have hA : ∀ k ∈ Finset.range (N.L0 + 1), A N x c d s i (s + k) = A N x c d' s i (s + k) :=
              fun k hk => A_dep2 N x c s i (s + k) d d' h (by simp at hk; omega)
            rw [Finset.sum_congr rfl fun k hk => by
              rw [hA k hk, q_dep N x c s d d' h i, XS_dep N x c s d d' b k h]]
          rw [hBS]
          by_cases ho : ord N x c d s i
          · rw [if_pos ho, if_pos ((ord_dep N x c s i d d' h).1 ho)]
          · rw [if_neg ho, if_neg (fun h' => ho ((ord_dep N x c s i d d' h).2 h'))]
        have hb := lintegral_blk N.μ N' s N.L0 hsN Φ' hΦ'm hΦ'd
        have hle : ∀ d : ℕ → DemandVec n, Ψ d ≤ ∫⁻ b, Φ' d b ∂(Measure.pi fun _ : Fin N.L0 => N.μ) := by
          intro d
          simp only [hΨ, hΦ']
          by_cases ho : ord N x c d s i
          · simp only [if_pos ho]
            unfold zbarE zE
            have hm : Measurable fun p : ℝ × (Fin N.L0 → DemandVec n) =>
                ENNReal.ofReal (ZS N x c s i d p.1 p.2) :=
              ((ZS_meas N x c s i).comp ((measurable_const.prodMk measurable_fst).prodMk
                measurable_snd)).ennreal_ofReal
            rw [lintegral_lintegral_swap hm.aemeasurable]
            exact lintegral_mono fun b => avg_le_BS N x c hN hsS hs0S s i d ho.2.2.1 b
          · simp [if_neg ho]
        calc ∫⁻ z, Ψ (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ)
            ≤ ∫⁻ z, ∫⁻ b, Φ' (padHist N' z) b ∂(Measure.pi fun _ : Fin N.L0 => N.μ)
                ∂(Measure.pi fun _ : Fin N' => N.μ) := lintegral_mono fun z => hle _
          _ = ∫⁻ z, Φ' (padHist N' z) (fun j => padHist N' z (s + j))
                ∂(Measure.pi fun _ : Fin N' => N.μ) := hb.symm
          _ = _ := lintegral_congr fun z => by simp only [hΦ']; rw [BS_block]

end OWMR.Asm

end Part8

section Part9

/-! Assembly, part 9: the request index sum and the explicit pathwise bound. -/

open MeasureTheory
open scoped ENNReal NNReal


namespace OWMR.Asm

variable {n : ℕ} (N : Network n) (x : InitState n) (c : ConChoice n)

lemma jE_lt (hsS : ∀ i, c.s i ≤ c.S i) (d : ℕ → DemandVec n) (s s' : ℕ) (i i' : Fin n)
    (ho : ord N x c d s i) (hss : s < s') :
    jE N x c s i d < jE N x c s' i' d := by
  obtain ⟨hs, ha, hq, -⟩ := ho
  unfold jE
  have hmem : i ∈ (List.finRange n).filter (fun j => decide (0 < q N x c d s j)) := by
    simp [hq]
  have hidx := List.idxOf_lt_length_of_mem hmem
  have hsplit : ∑ r ∈ Finset.range s', (if 0 < r ∧ act N x c d (r - 1) then
        ((List.finRange n).filter (fun j => decide (0 < q N x c d r j))).length else 0)
      ≥ ∑ r ∈ Finset.range s, (if 0 < r ∧ act N x c d (r - 1) then
        ((List.finRange n).filter (fun j => decide (0 < q N x c d r j))).length else 0)
        + ((List.finRange n).filter (fun j => decide (0 < q N x c d s j))).length := by
    rw [← if_pos (show 0 < s ∧ act N x c d (s - 1) from ⟨hs, ha⟩) (c := (0 < s ∧ act N x c d (s - 1)))
      (t := ((List.finRange n).filter (fun j => decide (0 < q N x c d s j))).length) (e := 0),
      ← Finset.sum_range_succ (fun r => if 0 < r ∧ act N x c d (r - 1) then
        ((List.finRange n).filter (fun j => decide (0 < q N x c d r j))).length else 0) s]
    exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hss)
  omega

lemma jE_inj (hsS : ∀ i, c.s i ≤ c.S i) (d : ℕ → DemandVec n) (s s' : ℕ) (i i' : Fin n)
    (ho : ord N x c d s i) (ho' : ord N x c d s' i') (h : jE N x c s i d = jE N x c s' i' d) :
    s = s' ∧ i = i' := by
  rcases lt_trichotomy s s' with hss | rfl | hss
  · exact absurd h (ne_of_lt (jE_lt N x c hsS d s s' i i' ho hss))
  · refine ⟨rfl, ?_⟩
    unfold jE at h
    have h' : ((List.finRange n).filter (fun j => decide (0 < q N x c d s j))).idxOf i
        = ((List.finRange n).filter (fun j => decide (0 < q N x c d s j))).idxOf i' := by omega
    have hmem : i ∈ (List.finRange n).filter (fun j => decide (0 < q N x c d s j)) := by
      simp [ho.2.2.1]
    have hmem' : i' ∈ (List.finRange n).filter (fun j => decide (0 < q N x c d s j)) := by
      simp [ho'.2.2.1]
    exact (List.idxOf_inj hmem).1 h'
  · exact absurd h (ne_of_gt (jE_lt N x c hsS d s' s i' i ho' hss))

/-- The tolerances `2^{-j}` of distinct ordinary requests sum to at most one. -/
lemma tol_sum (hsS : ∀ i, c.s i ≤ c.S i) (d : ℕ → DemandVec n) (T : ℕ) :
    ∑ s ∈ Finset.range T, ∑ i, (if ord N x c d s i then (2 : ℝ≥0∞)⁻¹ ^ jE N x c s i d else 0)
      ≤ 1 := by
  classical
  set S := ((Finset.range T) ×ˢ (Finset.univ : Finset (Fin n))).filter
    (fun p => ord N x c d p.1 p.2) with hS
  have e1 : ∑ s ∈ Finset.range T, ∑ i, (if ord N x c d s i then (2 : ℝ≥0∞)⁻¹ ^ jE N x c s i d else 0)
      = ∑ p ∈ S, (2 : ℝ≥0∞)⁻¹ ^ jE N x c p.1 p.2 d := by
    rw [← Finset.sum_product', hS, Finset.sum_filter]
  rw [e1]
  have hpos : ∀ p ∈ S, 1 ≤ jE N x c p.1 p.2 d := fun p _ => by unfold jE; omega
  have e2 : ∀ p ∈ S, (2 : ℝ≥0∞)⁻¹ ^ jE N x c p.1 p.2 d
      = 2⁻¹ * (2 : ℝ≥0∞)⁻¹ ^ (jE N x c p.1 p.2 d - 1) := fun p hp => by
    rw [← pow_succ', Nat.sub_add_cancel (hpos p hp)]
  rw [Finset.sum_congr rfl e2, ← Finset.mul_sum]
  have hinj : Set.InjOn (fun p : ℕ × Fin n => jE N x c p.1 p.2 d - 1) S := by
    intro p hp p' hp' h
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hS] at hp hp'
    have h1 := hpos p (by simpa [hS] using hp)
    have h2 := hpos p' (by simpa [hS] using hp')
    have h3 : jE N x c p.1 p.2 d = jE N x c p'.1 p'.2 d := by simp only at h; omega
    obtain ⟨e3, e4⟩ := jE_inj N x c hsS d p.1 p'.1 p.2 p'.2 hp.2 hp'.2 h3
    exact Prod.ext e3 e4
  rw [← Finset.sum_image (f := fun m => (2 : ℝ≥0∞)⁻¹ ^ m) hinj]
  calc 2⁻¹ * ∑ m ∈ S.image (fun p : ℕ × Fin n => jE N x c p.1 p.2 d - 1), (2 : ℝ≥0∞)⁻¹ ^ m
      ≤ 2⁻¹ * ∑' m : ℕ, (2 : ℝ≥0∞)⁻¹ ^ m := by gcongr; exact ENNReal.sum_le_tsum _
    _ = 1 := by
        rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
          ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

lemma whLoss_le_abs' (h p y : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) : whLoss h p y ≤ (h + p) * |y| := by
  unfold whLoss
  have h1 : max y 0 ≤ |y| := max_le (le_abs_self y) (abs_nonneg y)
  have h2 : max (-y) 0 ≤ |y| := max_le (neg_le_abs y) (abs_nonneg y)
  nlinarith [mul_le_mul_of_nonneg_left h1 hh, mul_le_mul_of_nonneg_left h2 hp]

/-- Before the first dispatch arrives, retailer inventory is explicit. -/
lemma netInv_init (d : ℕ → DemandVec n) (i : Fin n) (t : ℕ) (ht : t < N.L i) :
    Policy.netInv N x (conPolicy N x c).toPolicy () d i t
      = x.I i + ∑ s ∈ Finset.range (t + 1), (x.retPipe i s - ((d s i : ℝ≥0) : ℝ)) := by
  unfold Policy.netInv
  congr 1
  exact Finset.sum_congr rfl fun s hs => by
    simp only [Policy.retArrival, if_pos (show s < N.L i by simp at hs; omega)]

/-- Transient periods: preparation, the first `L₀` running periods and the start. -/
def TI (d : ℕ → DemandVec n) (t : ℕ) : Prop := ¬ (N.L0 + 1 ≤ t ∧ act N x c d (t - N.L0 - 1))

instance TIDec (d : ℕ → DemandVec n) (t : ℕ) : Decidable (TI N x c d t) := Classical.dec _

/-- Total demand before `t`. -/
def Dall (d : ℕ → DemandVec n) (t : ℕ) : ℝ := ∑ i, ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ)

lemma Dall_nonneg (d : ℕ → DemandVec n) (t : ℕ) : 0 ≤ Dall d t :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun s _ => NNReal.coe_nonneg _

/-- The transient constant. -/
def ctr : ℝ := (∑ i, N.K i + N.h * W0 N x)
  + (N.h + N.p) * (|∑ i, (IP N x c (fun _ => 0) 0 i - c.S i)| + 1)
  + ∑ i, (3 * N.K i + (N.h + N.p) * ((N.L0 + 1 : ℝ) * (|c.S i - IP N x c (fun _ => 0) 0 i| + 1)))

lemma IP0_indep (d : ℕ → DemandVec n) (i : Fin n) : IP N x c d 0 i = IP N x c (fun _ => 0) 0 i := by
  unfold IP; simp

/-- Explicit per-period terms of the cost bound. -/
def mrun (d : ℕ → DemandVec n) (t : ℕ) : ℝ :=
  (if act N x c d t then N.K0 * (if 0 < q0 N x c d t then 1 else 0)
      + ∑ i, N.h * (c.S i - Ph N x c d t i)
      + ∑ i ∈ Finset.univ.filter (fun i => ¬ c.batch i = true), N.K i else 0)
  + (if N.L0 ≤ t ∧ act N x c d (t - N.L0) then
      whLoss N.h N.p (Ypost N x c d (t - N.L0)
        - ∑ j ∈ Finset.range N.L0, ((∑ i, d (t - N.L0 + j) i : ℝ≥0) : ℝ)) else 0)
  + ∑ i, cH N i (Pos' N x c d t i - Dblk N d t i)

/-- Initial retailer terms. -/
def minit (d : ℕ → DemandVec n) : ℝ :=
  ∑ i, ∑ t ∈ Finset.range (N.L i), cH N i (x.I i + ∑ s ∈ Finset.range (t + 1),
    (x.retPipe i s - ((d s i : ℝ≥0) : ℝ)))

section expl

variable (θ : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)
  (hdisp : ∀ d t i, (conPolicy N x c).dispatch t d i = if act N x c d t then
        ∑ s ∈ Finset.range (t + 1),
          ((if c.batch i then shippedPath (q N x c d s i) (θ d s i)
                (fun k => A N x c d s i (s + k)) (t - s)
              else A N x c d s i t)
            - if s < t then (if c.batch i then
                shippedPath (q N x c d s i) (θ d s i) (fun k => A N x c d s i (s + k)) (t - 1 - s)
              else A N x c d s i (t - 1)) else 0)
        else if t = N.Tpipe - 1 ∧ i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
        else 0)
  (hord : ∀ d t, (conPolicy N x c).order t d = q0 N x c d t)
  (hident : ∀ d s i, 0 < s → act N x c d (s - 1) → 0 < q N x c d s i → c.batch i = true →
        ∃ σ : EngState n,
          θ d s i = conRule N c σ s (∑ r ∈ Finset.range s,
              (if 0 < r ∧ act N x c d (r - 1) then
                ((List.finRange n).filter (fun j => decide (0 < q N x c d r j))).length else 0)
            + ((List.finRange n).filter (fun j => decide (0 < q N x c d s j))).idxOf i + 1) i
              (q N x c d s i) ∧
          ∀ (ds : Fin N.L0 → DemandVec n) (k : ℕ), k ≤ N.L0 →
            idealAlloc N c.params σ s i (q N x c d s i) (padHist N.L0 ds) k = A N x c d s i (s + k) ∧
            idealDepletion N c.params σ s (padHist N.L0 ds) k
              = ∑ j, (c.S j - Ph N x c (fun r => if r < s then d r else padHist N.L0 ds (r - s))
                  (s + k) j))

include hdisp hord hident in
/-- The explicit pathwise cost bound. -/
lemma cost_explicit (hN : N.Standing) (hx : x.Valid) (hsS : ∀ i, c.s i ≤ c.S i) (hs0 : 0 ≤ c.s0)
    (hs0S : c.s0 ≤ c.S0) (hθ : ∀ d s i, 0 < θ d s i ∧ θ d s i < 1) (d : ℕ → DemandVec n)
    (T : ℕ) :
    ∑ t ∈ Finset.range T, Policy.periodCost N x (conPolicy N x c).toPolicy () d t
      ≤ minit N x d + ∑ t ∈ Finset.range T, (mrun N x c d t
          + 3 * ctr N x c * (if TI N x c d t then 1 + Dall d t else 0))
        + ∑ s ∈ Finset.range T, ∑ i, (if ord N x c d s i then
            Zexp N x c d s i (thE N x c s i d) else 0) := by
  have hh := hN.h_pos.le; have hp := hN.p_pos.le
  have hK := hN.K_nonneg
  have hbase := cost_path N x c θ hdisp hord hN hx hsS hs0 hs0S hθ d T
  -- the initial terms
  have hI1 : ∑ i, ∑ t ∈ Finset.range (N.L i),
      cH N i (Policy.netInv N x (conPolicy N x c).toPolicy () d i t) = minit N x d := by
    unfold minit
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun t ht => by
      rw [netInv_init N x c d i t (Finset.mem_range.1 ht)]
  -- the proxies
  have hI5 : ∑ s ∈ Finset.range T, ∑ i, (if ord N x c d s i then Zexp N x c d s i (θ d s i) else 0)
      = ∑ s ∈ Finset.range T, ∑ i, (if ord N x c d s i then
          Zexp N x c d s i (thE N x c s i d) else 0) :=
    Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by
      by_cases ho : ord N x c d s i
      · rw [if_pos ho, if_pos ho, theta_eq N x c θ hident d s i ho]
      · rw [if_neg ho, if_neg ho]
  -- per-period comparison
  have hDall := Dall_nonneg d
  have hctr0 : 0 ≤ ctr N x c := by
    unfold ctr
    have hW0 : 0 ≤ W0 N x := by
      unfold W0; obtain ⟨h1, h2, -⟩ := hx
      exact add_nonneg h1 (Finset.sum_nonneg fun s _ => h2 s)
    have h1 : 0 ≤ ∑ i, N.K i + N.h * W0 N x :=
      add_nonneg (Finset.sum_nonneg fun i _ => hK i) (mul_nonneg hh hW0)
    have h2 : 0 ≤ (N.h + N.p) * (|∑ i, (IP N x c (fun _ => 0) 0 i - c.S i)| + 1) :=
      mul_nonneg (by linarith) (by positivity)
    have h3 : 0 ≤ ∑ i, (3 * N.K i + (N.h + N.p) * ((N.L0 + 1 : ℝ)
        * (|c.S i - IP N x c (fun _ => 0) 0 i| + 1))) :=
      Finset.sum_nonneg fun i _ => add_nonneg (by linarith [hK i])
        (mul_nonneg (by linarith) (by positivity))
    linarith
  have hpt : ∀ t, ((if act N x c d t then
            N.K0 * (if 0 < q0 N x c d t then 1 else 0)
              + ∑ i ∈ Finset.univ.filter (fun i => ¬ c.batch i = true), N.K i
          else ∑ i, N.K i)
        + ((if act N x c d t then
              whLoss N.h N.p (V N x c d t - Cq N x c d t - X N x c d t)
                + ∑ i, N.h * (c.S i - Ph N x c d t i)
            else N.h * W0 N x)
          + ∑ i, cH N i (Pos N x c d t i - Dblk N d t i))
        + (if start N x c d t then
            ∑ i, (3 * N.K i + (N.h + N.p) * ((N.L0 + 1 : ℝ) * q N x c d t i)) else 0))
      ≤ mrun N x c d t + 3 * ctr N x c * (if TI N x c d t then 1 + Dall d t else 0) := by
    intro t
    have hPos : ∀ i, Pos N x c d t i = Pos' N x c d t i := fun i => by
      unfold Pos Pos'
      split_ifs with ha
      · rfl
      · rw [rP_prep N x c θ hdisp d t ha i]; rfl
    simp only [hPos]
    -- the transient indicators
    have hTI1 : ¬ act N x c d t → TI N x c d t := fun ha h => ha (act_mono' N x c d (by omega) h.2)
    have hTI2 : act N x c d t → ¬ (N.L0 ≤ t ∧ act N x c d (t - N.L0)) → TI N x c d t :=
      fun _ hn h => hn ⟨by omega, act_mono' N x c d (by omega) h.2⟩
    have hTI3 : start N x c d t → TI N x c d t := fun hs h => hs.2 (act_mono' N x c d (by omega) h.2)
    -- bounds of the transient terms
    have hY : ∀ i, IP N x c d t i = IP N x c (fun _ => 0) 0 i
        - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) := fun i => by
      rw [IP_eq, IP0_indep]
    have hDi : ∀ i, ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) ≤ Dall d t := fun i =>
      Finset.single_le_sum (f := fun i => ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ))
        (fun i _ => Finset.sum_nonneg fun s _ => NNReal.coe_nonneg _) (Finset.mem_univ i)
    set c1 := ∑ i, N.K i + N.h * W0 N x with hc1
    set c2 := (N.h + N.p) * (|∑ i, (IP N x c (fun _ => 0) 0 i - c.S i)| + 1) with hc2
    set c3 := ∑ i, (3 * N.K i + (N.h + N.p) * ((N.L0 + 1 : ℝ)
        * (|c.S i - IP N x c (fun _ => 0) 0 i| + 1))) with hc3
    have hc : ctr N x c = c1 + c2 + c3 := rfl
    have hc10 : 0 ≤ c1 := by
      have : 0 ≤ W0 N x := by
        unfold W0; obtain ⟨h1, h2, -⟩ := hx
        exact add_nonneg h1 (Finset.sum_nonneg fun s _ => h2 s)
      exact add_nonneg (Finset.sum_nonneg fun i _ => hK i) (mul_nonneg hh this)
    have hc20 : 0 ≤ c2 := mul_nonneg (by linarith) (by positivity)
    have hc30 : 0 ≤ c3 := Finset.sum_nonneg fun i _ => add_nonneg (by linarith [hK i])
      (mul_nonneg (by linarith) (by positivity))
    have hstart_b : (if start N x c d t then
        ∑ i, (3 * N.K i + (N.h + N.p) * ((N.L0 + 1 : ℝ) * q N x c d t i)) else 0)
        ≤ (if TI N x c d t then c3 * (1 + Dall d t) else 0) := by
      by_cases hs : start N x c d t
      · rw [if_pos hs, if_pos (hTI3 hs)]
        have hq : ∀ i, q N x c d t i = c.S i - IP N x c d t i := fun i =>
          q_start N x c d t hs.1 hs.2 i
        calc ∑ i, (3 * N.K i + (N.h + N.p) * ((N.L0 + 1 : ℝ) * q N x c d t i))
            ≤ (∑ i, (3 * N.K i + (N.h + N.p) * ((N.L0 + 1 : ℝ)
                * (|c.S i - IP N x c (fun _ => 0) 0 i| + 1)))) * (1 + Dall d t) := by
              rw [Finset.sum_mul]
              refine Finset.sum_le_sum fun i _ => ?_
              rw [hq i, hY i]
              have h1 : c.S i - (IP N x c (fun _ => 0) 0 i - ∑ s ∈ Finset.range t,
                  ((d s i : ℝ≥0) : ℝ)) ≤ (|c.S i - IP N x c (fun _ => 0) 0 i| + 1)
                    * (1 + Dall d t) := by
                have := le_abs_self (c.S i - IP N x c (fun _ => 0) 0 i)
                have := hDi i
                nlinarith [abs_nonneg (c.S i - IP N x c (fun _ => 0) 0 i), hDall t]
              have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ N.L0 + 1)
              have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ N.h + N.p)
              nlinarith [hK i, hDall t]
          _ = c3 * (1 + Dall d t) := rfl
      · rw [if_neg hs]; split_ifs <;> [exact mul_nonneg hc30 (by linarith [hDall t]); exact le_rfl]
    have hrun_b : (if act N x c d t then
          whLoss N.h N.p (V N x c d t - Cq N x c d t - X N x c d t) else 0)
        ≤ (if N.L0 ≤ t ∧ act N x c d (t - N.L0) then
            whLoss N.h N.p (Ypost N x c d (t - N.L0)
              - ∑ j ∈ Finset.range N.L0, ((∑ i, d (t - N.L0 + j) i : ℝ≥0) : ℝ)) else 0)
          + (if TI N x c d t then c2 * (1 + Dall d t) else 0) := by
      by_cases ha : act N x c d t
      · rw [if_pos ha]
        by_cases ha' : N.L0 ≤ t ∧ act N x c d (t - N.L0)
        · rw [if_pos ha', E_shift N x c d t ha'.1 ha'.2]
          have : 0 ≤ (if TI N x c d t then c2 * (1 + Dall d t) else 0) := by
            split_ifs; exacts [mul_nonneg hc20 (by linarith [hDall t]), le_rfl]
          linarith
        · rw [if_neg ha', if_pos (hTI2 ha ha'), E_trans N x c d t ha ha', zero_add]
          have h1 := whLoss_le_abs' N.h N.p (∑ i, (IP N x c d t i - c.S i)) hh hp
          have h2 : |∑ i, (IP N x c d t i - c.S i)| ≤ |∑ i, (IP N x c (fun _ => 0) 0 i - c.S i)|
              + Dall d t := by
            have e : ∑ i, (IP N x c d t i - c.S i) = ∑ i, (IP N x c (fun _ => 0) 0 i - c.S i)
                - Dall d t := by
              unfold Dall; simp only [hY]; rw [← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl fun i _ => by ring
            rw [e]
            calc _ ≤ |∑ i, (IP N x c (fun _ => 0) 0 i - c.S i)| + |Dall d t| := abs_sub _ _
              _ = _ := by rw [abs_of_nonneg (hDall t)]
          have h3 : (|∑ i, (IP N x c (fun _ => 0) 0 i - c.S i)| + Dall d t)
              ≤ (|∑ i, (IP N x c (fun _ => 0) 0 i - c.S i)| + 1) * (1 + Dall d t) := by
            nlinarith [abs_nonneg (∑ i, (IP N x c (fun _ => 0) 0 i - c.S i)), hDall t]
          calc _ ≤ (N.h + N.p) * |∑ i, (IP N x c d t i - c.S i)| := h1
            _ ≤ (N.h + N.p) * ((|∑ i, (IP N x c (fun _ => 0) 0 i - c.S i)| + 1)
                * (1 + Dall d t)) := mul_le_mul_of_nonneg_left (le_trans h2 h3) (by linarith)
            _ = c2 * (1 + Dall d t) := by rw [hc2]; ring
      · rw [if_neg ha]
        have h1 : 0 ≤ (if N.L0 ≤ t ∧ act N x c d (t - N.L0) then
            whLoss N.h N.p (Ypost N x c d (t - N.L0)
              - ∑ j ∈ Finset.range N.L0, ((∑ i, d (t - N.L0 + j) i : ℝ≥0) : ℝ)) else 0) := by
          split_ifs; exacts [whLoss_nonneg _ _ _ hh hp, le_rfl]
        have h2 : 0 ≤ (if TI N x c d t then c2 * (1 + Dall d t) else 0) := by
          split_ifs; exacts [mul_nonneg hc20 (by linarith [hDall t]), le_rfl]
        linarith
    have hprep_b : (if act N x c d t then (0 : ℝ) else ∑ i, N.K i + N.h * W0 N x)
        ≤ (if TI N x c d t then c1 * (1 + Dall d t) else 0) := by
      by_cases ha : act N x c d t
      · rw [if_pos ha]; split_ifs; exacts [mul_nonneg hc10 (by linarith [hDall t]), le_rfl]
      · rw [if_neg ha, if_pos (hTI1 ha)]
        nlinarith [hDall t, hc10]
    have hTIb : (if TI N x c d t then c1 * (1 + Dall d t) else 0)
        + (if TI N x c d t then c2 * (1 + Dall d t) else 0)
        + (if TI N x c d t then c3 * (1 + Dall d t) else 0)
        ≤ 3 * ctr N x c * (if TI N x c d t then 1 + Dall d t else 0) := by
      split_ifs
      · rw [hc]; nlinarith [hDall t, hc10, hc20, hc30]
      · simp
    unfold mrun
    by_cases ha : act N x c d t
    · simp only [if_pos ha] at hprep_b ⊢
      simp only [if_pos ha] at hrun_b
      linarith
    · simp only [if_neg ha] at hprep_b hrun_b ⊢
      linarith
  rw [hI1, hI5] at hbase
  have hsum := Finset.sum_le_sum fun t (_ : t ∈ Finset.range T) => hpt t
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  linarith

end expl

end OWMR.Asm

end Part9

section Part10

/-! Assembly, part 10: expectation tools (lead-time laws, newsvendor kernels), from stage 6. -/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open OWMR OWMR.Asm


namespace OWMR.S6


/-- Splitting off the first demand: `ρ^{⊗(T+1)} ≅ ρ ⊗ ρ^{⊗T}`. -/
lemma lintegral_pi_succ (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (T : ℕ)
    {F : ℝ≥0 × (Fin T → ℝ≥0) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F (z 0, Fin.tail z) ∂(Measure.pi fun _ : Fin (T + 1) => ρ)
      = ∫⁻ y, ∫⁻ z', F (y, z') ∂(Measure.pi fun _ : Fin T => ρ) ∂ρ := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (T + 1) => ρ) 0
  have key : ∫⁻ z, F (z 0, Fin.tail z) ∂(Measure.pi fun _ : Fin (T + 1) => ρ)
      = ∫⁻ z, F (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (T + 1) => ℝ≥0) 0 z)
          ∂(Measure.pi fun _ : Fin (T + 1) => ρ) := by
    refine lintegral_congr fun z => ?_
    simp [MeasurableEquiv.piFinSuccAbove_apply]
  rw [key, hmp.lintegral_comp hF, lintegral_prod _ hF.aemeasurable]

lemma measurable_psum (k : ℕ) : Measurable (fun z : Fin k → ℝ≥0 => ∑ j, (z j : ℝ)) :=
  Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real

lemma lintegral_law_zero (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] {F : ℝ → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ x, F x ∂((Measure.pi fun _ : Fin 0 => ρ).map fun z => ∑ j, (z j : ℝ)) = F 0 := by
  rw [lintegral_map hF (measurable_psum 0)]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, lintegral_const, measure_univ, mul_one]

lemma lintegral_law_succ (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (n : ℕ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂((Measure.pi fun _ : Fin (n + 1) => ρ).map fun z => ∑ j, (z j : ℝ))
      = ∫⁻ y, ∫⁻ x, F ((y : ℝ) + x)
          ∂((Measure.pi fun _ : Fin n => ρ).map fun z => ∑ j, (z j : ℝ)) ∂ρ := by
  rw [lintegral_map hF (measurable_psum _)]
  have hG : Measurable fun q : ℝ≥0 × (Fin n → ℝ≥0) => F ((q.1 : ℝ) + ∑ j, (q.2 j : ℝ)) :=
    hF.comp (measurable_fst.coe_nnreal_real.add (Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp measurable_snd).coe_nnreal_real))
  have key : ∫⁻ z, F (∑ j, (z j : ℝ)) ∂(Measure.pi fun _ : Fin (n + 1) => ρ)
      = ∫⁻ z, F (((z 0 : ℝ≥0) : ℝ) + ∑ j, ((Fin.tail z j : ℝ≥0) : ℝ))
          ∂(Measure.pi fun _ : Fin (n + 1) => ρ) := by
    refine lintegral_congr fun z => ?_
    simp [Fin.sum_univ_succ, Fin.tail]
  rw [key, lintegral_pi_succ ρ n hG]
  refine lintegral_congr fun y => ?_
  rw [lintegral_map (f := fun x => F ((y : ℝ) + x)) (hF.comp (measurable_const_add _))
    (measurable_psum n)]


/-! ### Newsvendor costs `y ↦ 𝔼[H (y - X)⁺ + p (X - y)⁺]` -/

noncomputable def nvCost {β : Type} [MeasurableSpace β] (P : Measure β) (X : β → ℝ)
    (H p y : ℝ) : ℝ :=
  ∫ b, (H * max (y - X b) 0 + p * max (X b - y) 0) ∂P

section nv

variable {β : Type} [MeasurableSpace β] (P : Measure β) [IsProbabilityMeasure P] (X : β → ℝ)

lemma nv_integrable (hX : Integrable X P) (H p y : ℝ) :
    Integrable (fun b => H * max (y - X b) 0 + p * max (X b - y) 0) P :=
  (((integrable_const y).sub hX).pos_part.const_mul _).add
    ((hX.sub (integrable_const y)).pos_part.const_mul _)

omit [IsProbabilityMeasure P] in
lemma nv_nonneg (H p y : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p) : 0 ≤ nvCost P X H p y :=
  integral_nonneg fun b =>
    add_nonneg (mul_nonneg hH (le_max_right _ _)) (mul_nonneg hp (le_max_right _ _))

lemma nv_lower (hX : Integrable X P) (H p y : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p) :
    H * (y - ∫ b, X b ∂P) ≤ nvCost P X H p y ∧ p * (∫ b, X b ∂P - y) ≤ nvCost P X H p y := by
  have hi := nv_integrable P X hX H p y
  constructor
  · have e : H * (y - ∫ b, X b ∂P) = ∫ b, H * (y - X b) ∂P := by
      rw [integral_const_mul, integral_sub (integrable_const y) hX, integral_const, probReal_univ,
        one_smul]
    rw [e]
    refine integral_mono ((((integrable_const y).sub hX)).const_mul H) hi fun b => ?_
    have h1 : H * (y - X b) ≤ H * max (y - X b) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hH
    have h2 : 0 ≤ p * max (X b - y) 0 := mul_nonneg hp (le_max_right _ _)
    simp only
    linarith
  · have e : p * (∫ b, X b ∂P - y) = ∫ b, p * (X b - y) ∂P := by
      rw [integral_const_mul, integral_sub hX (integrable_const y), integral_const, probReal_univ,
        one_smul]
    rw [e]
    refine integral_mono ((hX.sub (integrable_const y)).const_mul p) hi fun b => ?_
    have h1 : p * (X b - y) ≤ p * max (X b - y) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hp
    have h2 : 0 ≤ H * max (y - X b) 0 := mul_nonneg hH (le_max_right _ _)
    simp only
    linarith

lemma nv_lip (hX : Integrable X P) (H p : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p) (y y' : ℝ) :
    |nvCost P X H p y - nvCost P X H p y'| ≤ (H + p) * |y - y'| := by
  unfold nvCost
  rw [← integral_sub (nv_integrable P X hX H p y) (nv_integrable P X hX H p y')]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ b, |H * max (y - X b) 0 + p * max (X b - y) 0
          - (H * max (y' - X b) 0 + p * max (X b - y') 0)| ∂P
      ≤ ∫ _b, (H + p) * |y - y'| ∂P := by
        refine integral_mono ((nv_integrable P X hX H p y).sub
          (nv_integrable P X hX H p y')).abs (integrable_const _) fun b => ?_
        have k1 := abs_max_sub_max_le_abs (y - X b) (y' - X b) 0
        have k2 := abs_max_sub_max_le_abs (X b - y) (X b - y') 0
        rw [show y - X b - (y' - X b) = y - y' by ring] at k1
        rw [show X b - y - (X b - y') = -(y - y') by ring, abs_neg] at k2
        calc |H * max (y - X b) 0 + p * max (X b - y) 0
              - (H * max (y' - X b) 0 + p * max (X b - y') 0)|
            = |H * (max (y - X b) 0 - max (y' - X b) 0)
                + p * (max (X b - y) 0 - max (X b - y') 0)| := by ring_nf
          _ ≤ |H * (max (y - X b) 0 - max (y' - X b) 0)|
                + |p * (max (X b - y) 0 - max (X b - y') 0)| := abs_add_le _ _
          _ = H * |max (y - X b) 0 - max (y' - X b) 0|
                + p * |max (X b - y) 0 - max (X b - y') 0| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hH, abs_of_nonneg hp]
          _ ≤ H * |y - y'| + p * |y - y'| :=
              add_le_add (mul_le_mul_of_nonneg_left k1 hH) (mul_le_mul_of_nonneg_left k2 hp)
          _ = (H + p) * |y - y'| := by ring
    _ = (H + p) * |y - y'| := by simp [integral_const, probReal_univ]

lemma nv_continuous (hX : Integrable X P) (H p : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p) :
    Continuous (nvCost P X H p) := by
  have hL : LipschitzWith (Real.toNNReal (H + p)) (nvCost P X H p) := by
    refine LipschitzWith.of_dist_le_mul fun y y' => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by linarith)]
    exact nv_lip P X hX H p hH hp y y'
  exact hL.continuous

end nv

lemma whLoss_add (h p a b : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) :
    whLoss h p (a + b) ≤ whLoss h p a + whLoss h p b := by
  unfold whLoss
  have k1 : max (a + b) 0 ≤ max a 0 + max b 0 :=
    max_le (add_le_add (le_max_left _ _) (le_max_left _ _))
      (add_nonneg (le_max_right _ _) (le_max_right _ _))
  have k2 : max (-(a + b)) 0 ≤ max (-a) 0 + max (-b) 0 :=
    max_le (by linarith [le_max_left (-a) 0, le_max_left (-b) 0])
      (add_nonneg (le_max_right _ _) (le_max_right _ _))
  have := mul_le_mul_of_nonneg_left k1 hh
  have := mul_le_mul_of_nonneg_left k2 hp
  linarith

lemma whLoss_sum {ι : Type} (s : Finset ι) (h p : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p)
    (a : ι → ℝ) : whLoss h p (∑ i ∈ s, a i) ≤ ∑ i ∈ s, whLoss h p (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [whLoss]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (whLoss_add h p _ _ hh hp).trans (add_le_add le_rfl ih)

lemma whLoss_nonneg (h p y : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) : 0 ≤ whLoss h p y := by
  unfold whLoss
  exact add_nonneg (mul_nonneg hh (le_max_right _ _)) (mul_nonneg hp (le_max_right _ _))

/-! ### Integrability of lead-time demands -/

lemma integrable_marginal {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) :
    Integrable (fun x : ℝ≥0 => (x : ℝ)) (N.marginal i) := by
  unfold Network.marginal
  rw [integrable_map_measure measurable_coe_nnreal_real.aestronglyMeasurable
    (measurable_pi_apply i).aemeasurable]
  have h := integrable_toReal_of_lintegral_ne_top
    (f := fun x : DemandVec n => ((x i : ℝ≥0) : ℝ≥0∞))
    ((measurable_pi_apply i).coe_nnreal_ennreal.aemeasurable) (hN.mean_lt_top i).ne
  simpa [Function.comp_def] using h

lemma integrable_aggregate {n : ℕ} (N : Network n) (hN : N.Standing) :
    Integrable (fun x : ℝ≥0 => (x : ℝ)) N.aggregate := by
  unfold Network.aggregate
  have hm : Measurable fun x : DemandVec n => ∑ i, x i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  rw [integrable_map_measure measurable_coe_nnreal_real.aestronglyMeasurable hm.aemeasurable]
  have h : Integrable (fun x : DemandVec n => ∑ i, ((x i : ℝ≥0) : ℝ)) N.μ :=
    integrable_finsetSum _ fun i _ => by
      have h1 := integrable_toReal_of_lintegral_ne_top
        (f := fun x : DemandVec n => ((x i : ℝ≥0) : ℝ≥0∞))
        ((measurable_pi_apply i).coe_nnreal_ennreal.aemeasurable) (hN.mean_lt_top i).ne
      simpa using h1
  simpa [Function.comp_def, NNReal.coe_sum] using h

lemma integrable_psum (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : Integrable (fun x : ℝ≥0 => (x : ℝ)) ρ) (L : ℕ) :
    Integrable (fun z : Fin L → ℝ≥0 => ∑ j, (z j : ℝ)) (Measure.pi fun _ : Fin L => ρ) := by
  refine integrable_finsetSum _ fun j _ => ?_
  have hmp := measurePreserving_eval (μ := fun _ : Fin L => ρ) j
  exact (hmp.integrable_comp measurable_coe_nnreal_real.aestronglyMeasurable).2 hρ

/-- If `v → 0`, then `limsup (u + v) ≤ limsup u` in `ℝ≥0∞`. -/
lemma limsup_add_tendsto_zero (u v : ℕ → ℝ≥0∞) (hv : Tendsto v atTop (𝓝 0)) :
    limsup (fun n => u n + v n) atTop ≤ limsup u atTop := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ≥0∞) < ε := by exact_mod_cast hε
  have hev : ∀ᶠ n in atTop, u n + v n ≤ u n + ε :=
    (hv.eventually (ge_mem_nhds hε')).mono fun n hn => add_le_add le_rfl hn
  calc limsup (fun n => u n + v n) atTop ≤ limsup (fun n => u n + (ε : ℝ≥0∞)) atTop :=
        limsup_le_limsup hev
    _ = limsup u atTop + ε :=
        limsup_add_const atTop u _ (by isBoundedDefault) (by isBoundedDefault)


/-! ### Blocks of later demands -/

section block

variable {α : Type} [MeasurableSpace α] [Zero α]

/-- The sum of the `m` demands of periods `t, …, t+m-1` is independent of everything observed
before period `t`. -/
lemma lintegral_block (μ : Measure α) [IsProbabilityMeasure μ]
    (g : α → ℝ≥0) (hg : Measurable g) (TT t : ℕ) :
    ∀ (m : ℕ), t + m ≤ TT → ∀ (X : (ℕ → α) → ℝ), Measurable X →
      (∀ (d d' : ℕ → α), (∀ s < t, d s = d' s) → X d = X d') →
      ∀ (G0 : ℝ → ℝ≥0∞), Measurable G0 →
      ∫⁻ z, G0 (X (padHist TT z) - ∑ j ∈ Finset.range m, (g (padHist TT z (t + j)) : ℝ))
          ∂(Measure.pi fun _ : Fin TT => μ)
        = ∫⁻ z, ∫⁻ y, G0 (X (padHist TT z) - y)
            ∂((Measure.pi fun _ : Fin m => μ.map g).map fun w => ∑ j, (w j : ℝ))
          ∂(Measure.pi fun _ : Fin TT => μ) := by
  have : IsProbabilityMeasure (μ.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  intro m
  induction m with
  | zero =>
    intro _ X _ _ G0 hG0
    refine lintegral_congr fun z => ?_
    rw [lintegral_law_zero (μ.map g) (F := fun y => G0 (X (padHist TT z) - y))
      (hG0.comp (measurable_const.sub measurable_id))]
    simp
  | succ m ih =>
    intro htm X hX hXdep G0 hG0
    have hgs : ∀ j, Measurable fun d : ℕ → α => (g (d (t + j)) : ℝ) := fun j =>
      (hg.comp (measurable_pi_apply (t + j))).coe_nnreal_real
    have hS : Measurable fun d : ℕ → α => ∑ j ∈ Finset.range m, (g (d (t + j)) : ℝ) :=
      Finset.measurable_sum _ fun j _ => hgs j
    set Φ : (ℕ → α) → α → ℝ≥0∞ := fun d a =>
      G0 (X d - ∑ j ∈ Finset.range m, (g (d (t + j)) : ℝ) - (g a : ℝ)) with hΦ
    have hΦm : Measurable fun q : (ℕ → α) × α => Φ q.1 q.2 :=
      hG0.comp (((hX.comp measurable_fst).sub (hS.comp measurable_fst)).sub
        (hg.comp measurable_snd).coe_nnreal_real)
    have hΦdep : ∀ (d d' : ℕ → α) (a : α), (∀ s < t + m, d s = d' s) → Φ d a = Φ d' a := by
      intro d d' a h
      simp only [hΦ]
      rw [hXdep d d' (fun s hs => h s (by omega))]
      congr 3
      exact Finset.sum_congr rfl fun j hj => by
        rw [h (t + j) (by have := Finset.mem_range.1 hj; omega)]
    have hstep := lintegral_coord μ TT (t + m) (by omega) Φ hΦm hΦdep
    have hL : ∀ z : Fin TT → α, G0 (X (padHist TT z)
        - ∑ j ∈ Finset.range (m + 1), (g (padHist TT z (t + j)) : ℝ))
        = Φ (padHist TT z) (padHist TT z (t + m)) := by
      intro z
      simp only [hΦ, Finset.sum_range_succ]
      congr 1
      ring
    simp_rw [hL]
    rw [hstep]
    set G1 : ℝ → ℝ≥0∞ := fun y => ∫⁻ a, G0 (y - (g a : ℝ)) ∂μ with hG1
    have hG1m : Measurable G1 :=
      Measurable.lintegral_prod_right' (f := fun q : ℝ × α => G0 (q.1 - (g q.2 : ℝ)))
        (hG0.comp (measurable_fst.sub (hg.comp measurable_snd).coe_nnreal_real))
    have hih := ih (by omega) X hX hXdep G1 hG1m
    have hrw : ∀ z : Fin TT → α, ∫⁻ a, Φ (padHist TT z) a ∂μ
        = G1 (X (padHist TT z) - ∑ j ∈ Finset.range m, (g (padHist TT z (t + j)) : ℝ)) :=
      fun z => rfl
    simp_rw [hrw]
    rw [hih]
    refine lintegral_congr fun z => ?_
    set x0 := X (padHist TT z)
    rw [lintegral_law_succ (μ.map g) m (F := fun y => G0 (x0 - y))
      (hG0.comp (measurable_const.sub measurable_id))]
    have hswap : ∫⁻ y, G1 (x0 - y)
        ∂((Measure.pi fun _ : Fin m => μ.map g).map fun w => ∑ j, (w j : ℝ))
        = ∫⁻ b, ∫⁻ y, G0 (x0 - y - (b : ℝ))
          ∂((Measure.pi fun _ : Fin m => μ.map g).map fun w => ∑ j, (w j : ℝ)) ∂(μ.map g) := by
      have hrw2 : ∀ y : ℝ, G1 (x0 - y) = ∫⁻ b, G0 (x0 - y - (b : ℝ)) ∂(μ.map g) := by
        intro y
        simp only [hG1]
        rw [lintegral_map (f := fun b : ℝ≥0 => G0 (x0 - y - (b : ℝ)))
          (hG0.comp (measurable_const.sub measurable_coe_nnreal_real)) hg]
      simp_rw [hrw2]
      exact lintegral_lintegral_swap ((hG0.comp ((measurable_const.sub measurable_fst).sub
        measurable_snd.coe_nnreal_real)).aemeasurable)
    rw [hswap]
    refine lintegral_congr fun b => lintegral_congr fun y => ?_
    congr 1
    ring

end block

/-- The lead-time cost kernel: integrating a piecewise-linear cost against the law of a sum of
`m` i.i.d. demands. -/
lemma block_eval (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : Integrable (fun x : ℝ≥0 => (x : ℝ)) ρ) (m : ℕ) (Hc pc : ℝ) (hHc : 0 ≤ Hc) (hpc : 0 ≤ pc)
    (X : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Hc * max (X - y) 0 + pc * max (-(X - y)) 0)
        ∂((Measure.pi fun _ : Fin m => ρ).map fun w => ∑ j, (w j : ℝ))
      = ENNReal.ofReal (∫ w, (Hc * max (X - ∑ j, (w j : ℝ)) 0 + pc * max (∑ j, (w j : ℝ) - X) 0)
          ∂(Measure.pi fun _ : Fin m => ρ)) := by
  have hm : Measurable fun y : ℝ => ENNReal.ofReal (Hc * max (X - y) 0 + pc * max (-(X - y)) 0) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [lintegral_map hm (measurable_psum m)]
  simp only [neg_sub]
  rw [ofReal_integral_eq_lintegral_ofReal (nv_integrable _ _ (integrable_psum ρ hρ m) Hc pc X)
    (ae_of_all _ fun w => add_nonneg (mul_nonneg hHc (le_max_right _ _))
      (mul_nonneg hpc (le_max_right _ _)))]

lemma fL0_eq {n : ℕ} (N : Network n) (X : ℝ) :
    N.fL0 X = nvCost (Measure.pi fun _ : Fin N.L0 => N.aggregate) (fun w => ∑ j, (w j : ℝ)) N.h N.p X := by
  unfold Network.fL0 nvCost whLoss
  simp only [neg_sub]

lemma F_eq {n : ℕ} (N : Network n) (i : Fin n) (X : ℝ) :
    N.F i X = nvCost (Measure.pi fun _ : Fin (N.L i + 1) => N.marginal i) (fun w => ∑ j, (w j : ℝ))
      (N.H i) N.p X := rfl

lemma fL0_cont {n : ℕ} (N : Network n) (hN : N.Standing) : Continuous N.fL0 := by
  have : N.fL0 = nvCost (Measure.pi fun _ : Fin N.L0 => N.aggregate) (fun w => ∑ j, (w j : ℝ))
      N.h N.p := funext fun X => fL0_eq N X
  rw [this]
  exact nv_continuous _ _ (integrable_psum _ (integrable_aggregate N hN) _) _ _ hN.h_pos.le hN.p_pos.le

lemma fL0_lip {n : ℕ} (N : Network n) (hN : N.Standing) (y y' : ℝ) :
    |N.fL0 y - N.fL0 y'| ≤ (N.h + N.p) * |y - y'| := by
  rw [fL0_eq, fL0_eq]
  exact nv_lip _ _ (integrable_psum _ (integrable_aggregate N hN) _) _ _ hN.h_pos.le hN.p_pos.le y y'

lemma fL0_nonneg {n : ℕ} (N : Network n) (hN : N.Standing) (y : ℝ) : 0 ≤ N.fL0 y := by
  rw [fL0_eq]; exact nv_nonneg _ _ _ _ _ hN.h_pos.le hN.p_pos.le

lemma mean_agg_pos {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing) :
    0 < ∫⁻ x, (x : ℝ≥0∞) ∂N.aggregate := by
  unfold Network.aggregate
  rw [lintegral_map measurable_coe_nnreal_ennreal
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)]
  refine lt_of_lt_of_le (hN.mean_pos ⟨0, hn⟩) (lintegral_mono fun a => ?_)
  simp only [ENNReal.coe_finset_sum]
  exact Finset.single_le_sum (f := fun i => ((a i : ℝ≥0) : ℝ≥0∞)) (fun i _ => zero_le)
    (Finset.mem_univ _)

lemma mean_marg_pos {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n) :
    0 < ∫⁻ x, (x : ℝ≥0∞) ∂N.marginal i := by
  unfold Network.marginal
  rw [lintegral_map measurable_coe_nnreal_ennreal (measurable_pi_apply i)]
  exact hN.mean_pos i

lemma whLoss_le_abs (h p y : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) :
    whLoss h p y ≤ (h + p) * |y| := by
  unfold whLoss
  rcases le_or_gt 0 y with hy | hy
  · rw [max_eq_left hy, max_eq_right (by linarith), abs_of_nonneg hy]; nlinarith
  · rw [max_eq_right hy.le, max_eq_left (by linarith), abs_of_neg hy]; nlinarith


section coordx
variable {n : ℕ} (N : Network n)

lemma coord_le (T s : ℕ) (i : Fin n) :
    ∫⁻ z, ((padHist T z s i : ℝ≥0) : ℝ≥0∞) ∂(Measure.pi fun _ : Fin T => N.μ)
      ≤ ∫⁻ a, (a i : ℝ≥0∞) ∂N.μ := by
  by_cases hs : s < T
  · have e : ∀ z : Fin T → DemandVec n, padHist T z s = z ⟨s, hs⟩ := fun z => by
      simp [padHist, hs]
    simp_rw [e]
    rw [(measurePreserving_eval (fun _ : Fin T => N.μ) (⟨s, hs⟩ : Fin T)).lintegral_comp
      (f := fun a : DemandVec n => ((a i : ℝ≥0) : ℝ≥0∞)) (measurable_pi_apply i).coe_nnreal_ennreal]
  · have e : ∀ z : Fin T → DemandVec n, padHist T z s = 0 := fun z => by simp [padHist, hs]
    simp_rw [e]
    simp

lemma lin_exp (T k : ℕ) :
    ∫⁻ z, ENNReal.ofReal (1 + ∑ i, ∑ s ∈ Finset.range k, ((padHist T z s i : ℝ≥0) : ℝ))
        ∂(Measure.pi fun _ : Fin T => N.μ)
      ≤ 1 + k * ∑ i, ∫⁻ a, (a i : ℝ≥0∞) ∂N.μ := by
  have hD := measurable_padHist' (α := DemandVec n) T
  have e : ∀ z : Fin T → DemandVec n,
      ENNReal.ofReal (1 + ∑ i, ∑ s ∈ Finset.range k, ((padHist T z s i : ℝ≥0) : ℝ))
        = 1 + ∑ i, ∑ s ∈ Finset.range k, ((padHist T z s i : ℝ≥0) : ℝ≥0∞) := by
    intro z
    rw [ENNReal.ofReal_add zero_le_one (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun s _ =>
      NNReal.coe_nonneg _), ENNReal.ofReal_one, ENNReal.ofReal_sum_of_nonneg fun i _ =>
      Finset.sum_nonneg fun s _ => NNReal.coe_nonneg _]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun s _ => NNReal.coe_nonneg _]
    exact Finset.sum_congr rfl fun s _ => ENNReal.ofReal_coe_nnreal
  simp_rw [e]
  have hm : ∀ i s, Measurable fun z : Fin T → DemandVec n => ((padHist T z s i : ℝ≥0) : ℝ≥0∞) :=
    fun i s => ((measurable_pi_apply i).comp ((measurable_pi_apply s).comp hD)).coe_nnreal_ennreal
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_finsetSum (f := fun i (z : Fin T → DemandVec n) =>
      ∑ s ∈ Finset.range k, ((padHist T z s i : ℝ≥0) : ℝ≥0∞)) _
      fun i _ => Finset.measurable_sum _ fun s _ => hm i s]
  gcongr
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [lintegral_finsetSum (f := fun s (z : Fin T → DemandVec n) => ((padHist T z s i : ℝ≥0) : ℝ≥0∞))
    _ fun s _ => hm i s]
  calc ∑ s ∈ Finset.range k, ∫⁻ z, ((padHist T z s i : ℝ≥0) : ℝ≥0∞) ∂(Measure.pi fun _ : Fin T => N.μ)
      ≤ ∑ _s ∈ Finset.range k, ∫⁻ a, (a i : ℝ≥0∞) ∂N.μ :=
        Finset.sum_le_sum fun s _ => coord_le N T s i
    _ = k * ∫⁻ a, (a i : ℝ≥0∞) ∂N.μ := by simp

end coordx

/-! ### Dependence of the realized cost on the past, and the horizon extension -/

section depx

variable {n : ℕ} (N : Network n) (x : InitState n) (c : ConChoice n)

lemma A_dep3 (s : ℕ) (i : Fin n) (t' t : ℕ) (d d' : ℕ → DemandVec n)
    (h : ∀ r < t, d r = d' r) (hs : s ≤ t) (ht : t' ≤ t) :
    A N x c d s i t' = A N x c d' s i t' := by
  rw [A_eq, A_eq]
  have hq : ∀ r ≤ s, ∀ j, q N x c d r j = q N x c d' r j := fun r hr j =>
    q_dep N x c r d d' (fun r' hr' => h r' (by omega)) j
  have hV : V N x c d t' = V N x c d' t' := by
    unfold V
    exact Finset.sum_congr rfl fun r hr => q0_dep N x c r d d'
      (fun r' hr' => h r' (by simp at hr; omega))
  have hah : ahead N x c d s i = ahead N x c d' s i := by
    unfold ahead
    rw [Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun j _ =>
      hq r (by simp at hr; omega) j]
    rw [Finset.sum_congr rfl fun j _ => hq s le_rfl j]
  rw [hq s le_rfl i, hV, hah]

variable (θ : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)
  (hθd : ∀ d d' s, (∀ r < s, d r = d' r) → ∀ i, θ d s i = θ d' s i)
  (hdisp : ∀ d t i, (conPolicy N x c).dispatch t d i = if act N x c d t then
        ∑ s ∈ Finset.range (t + 1),
          ((if c.batch i then shippedPath (q N x c d s i) (θ d s i)
                (fun k => A N x c d s i (s + k)) (t - s)
              else A N x c d s i t)
            - if s < t then (if c.batch i then
                shippedPath (q N x c d s i) (θ d s i) (fun k => A N x c d s i (s + k)) (t - 1 - s)
              else A N x c d s i (t - 1)) else 0)
        else if t = N.Tpipe - 1 ∧ i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
        else 0)
  (hord : ∀ d t, (conPolicy N x c).order t d = q0 N x c d t)

include hθd hdisp in
lemma dispatch_dep (t : ℕ) (d d' : ℕ → DemandVec n) (h : ∀ r < t, d r = d' r) (i : Fin n) :
    (conPolicy N x c).dispatch t d i = (conPolicy N x c).dispatch t d' i := by
  rw [hdisp, hdisp]
  have ha := act_dep N x c t d d' h
  by_cases h1 : act N x c d t
  · rw [if_pos h1, if_pos (ha.1 h1)]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' : s ≤ t := by simp at hs; omega
    have hq : q N x c d s i = q N x c d' s i := q_dep N x c s d d' (fun r hr => h r (by omega)) i
    have hθ' : θ d s i = θ d' s i := hθd d d' s (fun r hr => h r (by omega)) i
    have hA : ∀ t' ≤ t, A N x c d s i t' = A N x c d' s i t' := fun t' ht' =>
      A_dep3 N x c s i t' t d d' h hs' ht'
    have hsh : ∀ k ≤ t - s, shippedPath (q N x c d s i) (θ d s i) (fun k => A N x c d s i (s + k)) k
        = shippedPath (q N x c d' s i) (θ d' s i) (fun k => A N x c d' s i (s + k)) k := by
      intro k hk
      rw [hq, hθ']
      exact ship_congr _ _ _ _ k fun k' hk' => hA (s + k') (by omega)
    rw [hsh (t - s) le_rfl, hA t le_rfl]
    by_cases hst : s < t
    · rw [if_pos hst, if_pos hst, hsh (t - 1 - s) (by omega), hA (t - 1) (by omega)]
    · rw [if_neg hst, if_neg hst]
  · rw [if_neg h1, if_neg (fun h' => h1 (ha.2 h'))]

include hθd hdisp hord in
lemma pc_dep (t : ℕ) (d d' : ℕ → DemandVec n) (h : ∀ r < t + 1, d r = d' r) :
    Policy.periodCost N x (conPolicy N x c).toPolicy () d t
      = Policy.periodCost N x (conPolicy N x c).toPolicy () d' t := by
  have hO : ∀ s ≤ t, (conPolicy N x c).order s d = (conPolicy N x c).order s d' := fun s hs => by
    rw [hord, hord]; exact q0_dep N x c s d d' (fun r hr => h r (by omega))
  have hD : ∀ s ≤ t, ∀ i, (conPolicy N x c).dispatch s d i = (conPolicy N x c).dispatch s d' i :=
    fun s hs i => dispatch_dep N x c θ hθd hdisp s d d' (fun r hr => h r (by omega)) i
  have hS : ∀ s ≤ t, Policy.supArrival N x (conPolicy N x c).toPolicy () d s
      = Policy.supArrival N x (conPolicy N x c).toPolicy () d' s := fun s hs => by
    unfold Policy.supArrival
    split_ifs
    · rfl
    · exact hO (s - N.L0) (by omega)
  have hR : ∀ s ≤ t, ∀ i, Policy.retArrival N x (conPolicy N x c).toPolicy () d i s
      = Policy.retArrival N x (conPolicy N x c).toPolicy () d' i s := fun s hs i => by
    unfold Policy.retArrival
    split_ifs
    · rfl
    · exact hD (s - N.L i) (by omega) i
  have hW : Policy.whStock N x (conPolicy N x c).toPolicy () d t
      = Policy.whStock N x (conPolicy N x c).toPolicy () d' t := by
    unfold Policy.whStock
    congr 1
    exact Finset.sum_congr rfl fun s hs => by
      have hs' : s ≤ t := by simp at hs; omega
      rw [hS s hs']
      congr 1
      exact Finset.sum_congr rfl fun i _ => hD s hs' i
  have hI : ∀ i, Policy.netInv N x (conPolicy N x c).toPolicy () d i t
      = Policy.netInv N x (conPolicy N x c).toPolicy () d' i t := fun i => by
    unfold Policy.netInv
    congr 1
    exact Finset.sum_congr rfl fun s hs => by
      have hs' : s ≤ t := by simp at hs; omega
      rw [hR s hs' i, h s (by omega)]
  have e1 : (conPolicy N x c).toPolicy.order t () d = (conPolicy N x c).toPolicy.order t () d' :=
    hO t le_rfl
  have e2 : ∀ i, (conPolicy N x c).toPolicy.dispatch t () d i
      = (conPolicy N x c).toPolicy.dispatch t () d' i := fun i => hD t le_rfl i
  unfold Policy.periodCost
  rw [hW, e1]
  simp only [hI, e2]

include hθd hdisp hord in
lemma cost_dep (T : ℕ) (d d' : ℕ → DemandVec n) (h : ∀ r < T, d r = d' r) :
    ∑ t ∈ Finset.range T, ENNReal.ofReal (Policy.periodCost N x (conPolicy N x c).toPolicy () d t)
      = ∑ t ∈ Finset.range T,
          ENNReal.ofReal (Policy.periodCost N x (conPolicy N x c).toPolicy () d' t) :=
  Finset.sum_congr rfl fun t ht => by
    rw [pc_dep N x c θ hθd hdisp hord t d d' (fun r hr => h r (by simp at ht; omega))]

include hθd hdisp hord in
lemma expCost_le (T M : ℕ) :
    expCost N x (conPolicy N x c).toPolicy (Measure.dirac ()) T
      ≤ ∫⁻ z, ∑ t ∈ Finset.range T, ENNReal.ofReal
          (Policy.periodCost N x (conPolicy N x c).toPolicy () (padHist (T + M) z) t)
        ∂(Measure.pi fun _ : Fin (T + M) => N.μ) := by
  unfold expCost
  rw [Measure.dirac_prod]
  refine (lintegral_map_le _ _).trans ?_
  exact horizon_le N.μ T (T + M) (by omega) (fun d => ∑ t ∈ Finset.range T, ENNReal.ofReal
    (Policy.periodCost N x (conPolicy N x c).toPolicy () d t)) (cost_dep N x c θ hθd hdisp hord T)

end depx

/-! ### Kernels: integrating a block of fresh demands -/

section ker

variable {n : ℕ} (N : Network n)

lemma lintegral_pi_map {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    [IsProbabilityMeasure μ] (g : α → β) (hg : Measurable g) (m : ℕ)
    (G : (Fin m → β) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ b, G (fun j => g (b j)) ∂(Measure.pi fun _ : Fin m => μ)
      = ∫⁻ w, G w ∂(Measure.pi fun _ : Fin m => μ.map g) := by
  have : IsProbabilityMeasure (μ.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  have e := Measure.pi_map_pi (μ := fun _ : Fin m => μ) (f := fun _ => g) (fun _ => hg.aemeasurable)
  have hmf : Measurable (fun (x : Fin m → α) (i : Fin m) => g (x i)) :=
    measurable_pi_lambda _ fun j => hg.comp (measurable_pi_apply j)
  rw [← e, lintegral_map hG hmf]

lemma integrable_Psum (hN : N.Standing) (P : Finset (Fin n)) :
    Integrable (fun x : ℝ≥0 => (x : ℝ)) (N.μ.map fun a : DemandVec n => ∑ i ∈ P, a i) := by
  have hm : Measurable fun x : DemandVec n => ∑ i ∈ P, x i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  rw [integrable_map_measure measurable_coe_nnreal_real.aestronglyMeasurable hm.aemeasurable]
  have h : Integrable (fun x : DemandVec n => ∑ i ∈ P, ((x i : ℝ≥0) : ℝ)) N.μ :=
    integrable_finsetSum _ fun i _ => by
      have h1 := integrable_toReal_of_lintegral_ne_top
        (f := fun x : DemandVec n => ((x i : ℝ≥0) : ℝ≥0∞))
        ((measurable_pi_apply i).coe_nnreal_ennreal.aemeasurable) (hN.mean_lt_top i).ne
      simpa using h1
  simpa [Function.comp_def, NNReal.coe_sum] using h

lemma meas_whLoss (h p : ℝ) : Measurable fun y : ℝ => whLoss h p y := by
  unfold whLoss; fun_prop

lemma ker_fL0 (hN : N.Standing) (y : ℝ) :
    ∫⁻ b, ENNReal.ofReal (whLoss N.h N.p (y - ∑ j, ((∑ i, b j i : ℝ≥0) : ℝ)))
        ∂(Measure.pi fun _ : Fin N.L0 => N.μ)
      = ENNReal.ofReal (N.fL0 y) := by
  have hg : Measurable fun a : DemandVec n => ∑ i, a i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hG : Measurable fun w : Fin N.L0 → ℝ≥0 =>
      ENNReal.ofReal (whLoss N.h N.p (y - ∑ j, (w j : ℝ))) :=
    ((meas_whLoss N.h N.p).comp (measurable_const.sub (measurable_psum N.L0))).ennreal_ofReal
  refine (lintegral_pi_map N.μ (fun a : DemandVec n => ∑ i, a i) hg N.L0
    (fun w => ENNReal.ofReal (whLoss N.h N.p (y - ∑ j, (w j : ℝ)))) hG).trans ?_
  have hagg : N.μ.map (fun a : DemandVec n => ∑ i, a i) = N.aggregate := rfl
  rw [hagg]
  unfold Network.fL0
  have hint : Integrable (fun w : Fin N.L0 → ℝ≥0 => whLoss N.h N.p (y - ∑ j, (w j : ℝ)))
      (Measure.pi fun _ : Fin N.L0 => N.aggregate) := by
    have := nv_integrable (Measure.pi fun _ : Fin N.L0 => N.aggregate) (fun w => ∑ j, (w j : ℝ))
      (integrable_psum _ (integrable_aggregate N hN) _) N.h N.p y
    refine this.congr (ae_of_all _ fun w => ?_)
    unfold whLoss; simp only [neg_sub]
  rw [ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun w => whLoss_nonneg _ _ _ hN.h_pos.le hN.p_pos.le)]

lemma ker_F (hN : N.Standing) (i : Fin n) (y : ℝ) :
    ∫⁻ b, ENNReal.ofReal (cH N i (y - ∑ j, ((b j i : ℝ≥0) : ℝ)))
        ∂(Measure.pi fun _ : Fin (N.L i + 1) => N.μ)
      = ENNReal.ofReal (N.F i y) := by
  have hg : Measurable fun a : DemandVec n => a i := measurable_pi_apply i
  have hcH : Measurable fun y => cH N i y := by unfold cH; fun_prop
  have hG : Measurable fun w : Fin (N.L i + 1) → ℝ≥0 =>
      ENNReal.ofReal (cH N i (y - ∑ j, (w j : ℝ))) :=
    (hcH.comp (measurable_const.sub (measurable_psum _))).ennreal_ofReal
  refine (lintegral_pi_map N.μ (fun a : DemandVec n => a i) hg (N.L i + 1)
    (fun w => ENNReal.ofReal (cH N i (y - ∑ j, (w j : ℝ)))) hG).trans ?_
  have hmar : N.μ.map (fun a : DemandVec n => a i) = N.marginal i := rfl
  rw [hmar]
  unfold Network.F
  have hint := nv_integrable (Measure.pi fun _ : Fin (N.L i + 1) => N.marginal i)
    (fun w => ∑ j, (w j : ℝ)) (integrable_psum _ (integrable_marginal N hN i) _) (N.H i) N.p y
  rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun w => add_nonneg
    (mul_nonneg (hN.H_pos i).le (le_max_right _ _)) (mul_nonneg hN.p_pos.le (le_max_right _ _)))]
  refine lintegral_congr fun w => ?_
  unfold cH; simp only [neg_sub]

/-- The supplier shortage probability over a lead time. -/
def gsh (y : ℝ) : ℝ :=
  ((Measure.pi fun _ : Fin N.L0 => N.aggregate) {w | y < ∑ j, (w j : ℝ)}).toReal

lemma ker_sh (y : ℝ) :
    ∫⁻ b, (if y < ∑ j, ((∑ i, b j i : ℝ≥0) : ℝ) then (1 : ℝ≥0∞) else 0)
        ∂(Measure.pi fun _ : Fin N.L0 => N.μ)
      = ENNReal.ofReal (gsh N y) := by
  have hg : Measurable fun a : DemandVec n => ∑ i, a i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hset : MeasurableSet {w : Fin N.L0 → ℝ≥0 | y < ∑ j, (w j : ℝ)} :=
    measurableSet_lt measurable_const (measurable_psum N.L0)
  have hG : Measurable fun w : Fin N.L0 → ℝ≥0 =>
      (if y < ∑ j, (w j : ℝ) then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite hset measurable_const measurable_const
  refine (lintegral_pi_map N.μ (fun a : DemandVec n => ∑ i, a i) hg N.L0
    (fun w => if y < ∑ j, (w j : ℝ) then (1 : ℝ≥0∞) else 0) hG).trans ?_
  have hagg : N.μ.map (fun a : DemandVec n => ∑ i, a i) = N.aggregate := rfl
  rw [hagg]
  have e : ∀ w : Fin N.L0 → ℝ≥0, (if y < ∑ j, (w j : ℝ) then (1 : ℝ≥0∞) else 0)
      = Set.indicator {w : Fin N.L0 → ℝ≥0 | y < ∑ j, (w j : ℝ)} (fun _ => 1) w := fun w => by
    simp [Set.indicator_apply]
  simp_rw [e]
  rw [lintegral_indicator_const hset, one_mul]
  unfold gsh
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma gsh_nonneg (y : ℝ) : 0 ≤ gsh N y := ENNReal.toReal_nonneg

lemma gsh_le_one (y : ℝ) : gsh N y ≤ 1 := by
  unfold gsh
  have h1 : (Measure.pi fun _ : Fin N.L0 => N.aggregate) {w | y < ∑ j, (w j : ℝ)} ≤ 1 :=
    prob_le_one
  have := ENNReal.toReal_mono ENNReal.one_ne_top h1
  simpa using this

lemma gsh_anti : Antitone (gsh N) := by
  intro a b hab
  unfold gsh
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw ⊢
  linarith

lemma meas_sup (L : ℕ) : Measurable fun w : Fin L → ℝ≥0 => (Finset.univ.sup w : ℝ≥0) := by
  have key : ∀ s : Finset (Fin L), Measurable fun w : Fin L → ℝ≥0 => s.sup w := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sup_empty]; exact measurable_const
    | insert j s hj ih =>
      simp only [Finset.sup_insert]
      exact (measurable_pi_apply j).sup ih
  exact key _

lemma sup_le_sum (L : ℕ) (w : Fin L → ℝ≥0) :
    ((Finset.univ.sup w : ℝ≥0) : ℝ) ≤ ∑ j, (w j : ℝ) := by
  have : (Finset.univ.sup w : ℝ≥0) ≤ ∑ j, w j :=
    Finset.sup_le fun j _ => Finset.single_le_sum (f := w) (fun _ _ => zero_le)
      (Finset.mem_univ j)
  exact_mod_cast this

lemma ker_vmax (hN : N.Standing) (P : Finset (Fin n)) (y : ℝ) :
    ∫⁻ b, ENNReal.ofReal (max (((Finset.univ.sup fun j : Fin N.L0 => ∑ i ∈ P, b j i : ℝ≥0) : ℝ)
        - y) 0) ∂(Measure.pi fun _ : Fin N.L0 => N.μ)
      = ENNReal.ofReal (∫ w, max (((Finset.univ.sup w : ℝ≥0) : ℝ) - y) 0
          ∂(Measure.pi fun _ : Fin N.L0 => N.μ.map (fun a : DemandVec n => ∑ i ∈ P, a i))) := by
  have hg : Measurable fun a : DemandVec n => ∑ i ∈ P, a i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have : IsProbabilityMeasure (N.μ.map fun a : DemandVec n => ∑ i ∈ P, a i) :=
    Measure.isProbabilityMeasure_map hg.aemeasurable
  have hms : Measurable fun w : Fin N.L0 → ℝ≥0 => max (((Finset.univ.sup w : ℝ≥0) : ℝ) - y) 0 :=
    ((meas_sup N.L0).coe_nnreal_real.sub measurable_const).max measurable_const
  refine (lintegral_pi_map N.μ (fun a : DemandVec n => ∑ i ∈ P, a i) hg N.L0
    (fun w => ENNReal.ofReal (max (((Finset.univ.sup w : ℝ≥0) : ℝ) - y) 0)) hms.ennreal_ofReal).trans ?_
  have hint : Integrable (fun w : Fin N.L0 → ℝ≥0 => max (((Finset.univ.sup w : ℝ≥0) : ℝ) - y) 0)
      (Measure.pi fun _ : Fin N.L0 => N.μ.map (fun a : DemandVec n => ∑ i ∈ P, a i)) := by
    refine Integrable.mono' ((integrable_psum _ (integrable_Psum N hN P) N.L0).add
      (integrable_const |y|)) hms.aestronglyMeasurable (ae_of_all _ fun w => ?_)
    have h1 := sup_le_sum N.L0 w
    have h2 : (0 : ℝ) ≤ ((Finset.univ.sup w : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    have h3 : 0 ≤ ∑ j, (w j : ℝ) := Finset.sum_nonneg fun j _ => NNReal.coe_nonneg _
    have h4 := neg_abs_le y
    have h5 := abs_nonneg y
    simp only [Pi.add_apply]
    refine max_le ?_ ?_ <;> linarith
  rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun w => le_max_right _ _)]

lemma ker_sum (m : ℕ) :
    ∫⁻ b, ENNReal.ofReal (∑ j, ∑ i, ((b j i : ℝ≥0) : ℝ)) ∂(Measure.pi fun _ : Fin m => N.μ)
      = m * ∑ i, ∫⁻ a, (a i : ℝ≥0∞) ∂N.μ := by
  have e : ∀ b : Fin m → DemandVec n, ENNReal.ofReal (∑ j, ∑ i, ((b j i : ℝ≥0) : ℝ))
      = ∑ j, ∑ i, ((b j i : ℝ≥0) : ℝ≥0∞) := fun b => by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => Finset.sum_nonneg fun i _ => NNReal.coe_nonneg _)]
    exact Finset.sum_congr rfl fun j _ => by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => NNReal.coe_nonneg _)]
      exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_coe_nnreal
  simp_rw [e]
  rw [lintegral_finset_sum _ (fun j _ => Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp (measurable_pi_apply j)).coe_nnreal_ennreal)]
  have h2 : ∀ j : Fin m, ∫⁻ b, ∑ i, ((b j i : ℝ≥0) : ℝ≥0∞) ∂(Measure.pi fun _ : Fin m => N.μ)
      = ∑ i, ∫⁻ a, (a i : ℝ≥0∞) ∂N.μ := fun j => by
    rw [lintegral_finset_sum _ (fun i _ =>
      ((measurable_pi_apply i).comp (measurable_pi_apply j)).coe_nnreal_ennreal)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hmp := measurePreserving_eval (μ := fun _ : Fin m => N.μ) j
    exact hmp.lintegral_comp (f := fun a : DemandVec n => (a i : ℝ≥0∞))
      (measurable_pi_apply i).coe_nnreal_ennreal
  simp_rw [h2]
  simp [Finset.sum_const, Finset.card_univ]

end ker

end OWMR.S6

end Part10

section Part11

/-! Assembly, part 11: long-run rates of the cost components. -/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open OWMR OWMR.S6


namespace OWMR.Asm

/-! ### Linear growth with a given rate -/

/-- `F` grows at most at rate `r`. -/
def LR (F : ℕ → ℝ≥0∞) (r : ℝ≥0∞) : Prop := ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ T : ℕ, F T ≤ T * r + C

lemma LR.mono {F G : ℕ → ℝ≥0∞} {r : ℝ≥0∞} (h : ∀ T, F T ≤ G T) (hG : LR G r) : LR F r := by
  obtain ⟨C, hC, hb⟩ := hG
  exact ⟨C, hC, fun T => (h T).trans (hb T)⟩

lemma LR.rate {F : ℕ → ℝ≥0∞} {r r' : ℝ≥0∞} (hr : r ≤ r') (hF : LR F r) : LR F r' := by
  obtain ⟨C, hC, hb⟩ := hF
  exact ⟨C, hC, fun T => (hb T).trans (by gcongr)⟩

lemma LR.add {F G : ℕ → ℝ≥0∞} {r s : ℝ≥0∞} (hF : LR F r) (hG : LR G s) :
    LR (fun T => F T + G T) (r + s) := by
  obtain ⟨C1, hC1, h1⟩ := hF
  obtain ⟨C2, hC2, h2⟩ := hG
  refine ⟨C1 + C2, ENNReal.add_ne_top.2 ⟨hC1, hC2⟩, fun T => ?_⟩
  calc F T + G T ≤ (T * r + C1) + (T * s + C2) := add_le_add (h1 T) (h2 T)
    _ = T * (r + s) + (C1 + C2) := by rw [mul_add]; ring

lemma LR.cmul {F : ℕ → ℝ≥0∞} {r : ℝ≥0∞} (a : ℝ≥0∞) (ha : a ≠ ∞) (hF : LR F r) :
    LR (fun T => a * F T) (a * r) := by
  obtain ⟨C, hC, h⟩ := hF
  refine ⟨a * C, ENNReal.mul_ne_top ha hC, fun T => ?_⟩
  calc a * F T ≤ a * (T * r + C) := by gcongr; exact h T
    _ = T * (a * r) + a * C := by ring

lemma LR.zero_rate {F : ℕ → ℝ≥0∞} (C : ℝ≥0∞) (hC : C ≠ ∞) (h : ∀ T, F T ≤ C) : LR F 0 :=
  ⟨C, hC, fun T => by simpa using h T⟩

lemma LR.sum {ι : Type} (s : Finset ι) (F : ι → ℕ → ℝ≥0∞) (r : ι → ℝ≥0∞)
    (h : ∀ i ∈ s, LR (F i) (r i)) : LR (fun T => ∑ i ∈ s, F i T) (∑ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, ENNReal.zero_ne_top, fun T => by simp⟩
  | insert j s hj ih =>
    have h1 := h j (Finset.mem_insert_self j s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    simp only [Finset.sum_insert hj]
    exact h1.add h2

lemma LR.shift {F : ℕ → ℝ≥0∞} {r : ℝ≥0∞} (L : ℕ) (hr : r ≠ ∞) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (h : ∀ T, F T ≤ ((T + L : ℕ) : ℝ≥0∞) * r + C) : LR F r := by
  refine ⟨L * r + C, ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top L) hr, hC⟩,
    fun T => (h T).trans (le_of_eq ?_)⟩
  push_cast; ring

lemma min_add_le' (a b c d : ℝ≥0∞) : min (a + b) (c + d) ≤ min a c + b + d := by
  rcases le_total a c with h | h
  · rw [min_eq_left h]
    calc min (a + b) (c + d) ≤ a + b := min_le_left _ _
      _ ≤ a + b + d := le_self_add
  · rw [min_eq_right h]
    calc min (a + b) (c + d) ≤ c + d := min_le_right _ _
      _ ≤ c + b + d := by rw [add_assoc]; exact add_le_add le_rfl le_add_self

/-- The average of a quantity with linear growth. -/
lemma LR.limsup {F : ℕ → ℝ≥0∞} {r : ℝ≥0∞} (hF : LR F r) :
    Filter.limsup (fun T : ℕ => (T : ℝ≥0∞)⁻¹ * F T) Filter.atTop ≤ r := by
  obtain ⟨C, hCf, hC⟩ := hF
  calc Filter.limsup (fun T : ℕ => (T : ℝ≥0∞)⁻¹ * F T) Filter.atTop
      ≤ Filter.limsup (fun T : ℕ => r + (T : ℝ≥0∞)⁻¹ * C) Filter.atTop := by
        refine Filter.limsup_le_limsup ?_
        filter_upwards [Filter.eventually_ge_atTop 1] with T hT
        have hT0 : (T : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
        calc (T : ℝ≥0∞)⁻¹ * F T ≤ (T : ℝ≥0∞)⁻¹ * (T * r + C) := by gcongr; exact hC T
          _ = r + (T : ℝ≥0∞)⁻¹ * C := by
            rw [mul_add, ← mul_assoc, ENNReal.inv_mul_cancel hT0 (ENNReal.natCast_ne_top T), one_mul]
    _ ≤ Filter.limsup (fun _ : ℕ => r) Filter.atTop :=
        limsup_add_tendsto_zero (fun _ => r) (fun T : ℕ => (T : ℝ≥0∞)⁻¹ * C) (by
          simpa using ENNReal.Tendsto.mul_const ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hCf))
    _ = r := Filter.limsup_const r

/-! ### Generic tools -/

lemma sum_lintegral_le {β ι : Type} [MeasurableSpace β] (μ : Measure β) (s : Finset ι)
    (f : ι → β → ℝ≥0∞) : ∑ i ∈ s, ∫⁻ b, f i b ∂μ ≤ ∫⁻ b, ∑ i ∈ s, f i b ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    calc ∫⁻ b, f j b ∂μ + ∑ i ∈ s, ∫⁻ b, f i b ∂μ ≤ ∫⁻ b, f j b ∂μ + ∫⁻ b, ∑ i ∈ s, f i b ∂μ :=
          add_le_add le_rfl ih
      _ ≤ ∫⁻ b, (f j b + ∑ i ∈ s, f i b) ∂μ := le_lintegral_add _ _

/-- Shifting a sum by `L` periods. -/
lemma shift_le (G : ℕ → ℝ≥0∞) (T L : ℕ) :
    ∑ t ∈ Finset.range T, (if L ≤ t then G (t - L) else 0) ≤ ∑ t ∈ Finset.range T, G t := by
  calc ∑ t ∈ Finset.range T, (if L ≤ t then G (t - L) else 0)
      ≤ ∑ t ∈ Finset.range (L + T), (if L ≤ t then G (t - L) else 0) :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
    _ = ∑ t ∈ Finset.range L, (if L ≤ t then G (t - L) else 0)
        + ∑ t ∈ Finset.range T, (if L ≤ L + t then G (L + t - L) else 0) := Finset.sum_range_add _ _ _
    _ = ∑ t ∈ Finset.range T, G t := by
        rw [Finset.sum_eq_zero fun t ht => if_neg (by simp at ht; omega), zero_add]
        exact Finset.sum_congr rfl fun t _ => by
          rw [if_pos (show L ≤ L + t by omega), Nat.add_sub_cancel_left]

section long

variable {n : ℕ} (N : Network n) (x : InitState n) (c : ConChoice n)

/-- The horizon margin. -/
def Mh : ℕ := N.Tpipe + N.L0 + 1

lemma Dall_meas (t : ℕ) : Measurable fun d : ℕ → DemandVec n => Dall d t :=
  Finset.measurable_sum _ fun i _ => meas_dsum t i

lemma Dall_mono (d : ℕ → DemandVec n) {t t' : ℕ} (h : t ≤ t') : Dall d t ≤ Dall d t' :=
  Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.2 h) fun _ _ _ => NNReal.coe_nonneg _

lemma dsum_le_Dall (d : ℕ → DemandVec n) (t : ℕ) (i : Fin n) :
    ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) ≤ Dall d t :=
  Finset.single_le_sum (f := fun i => ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ))
    (fun i _ => Finset.sum_nonneg fun s _ => NNReal.coe_nonneg _) (Finset.mem_univ i)

/-- The block lemma with an indicator and a past-measurable state. -/
lemma blk_ind (N' t m : ℕ) (htm : t + m ≤ N') (E : (ℕ → DemandVec n) → Prop) [DecidablePred E]
    (hE : MeasurableSet {d | E d}) (hEd : ∀ d d' : ℕ → DemandVec n, (∀ r < t, d r = d' r) → (E d ↔ E d'))
    (Y : (ℕ → DemandVec n) → ℝ) (hY : Measurable Y)
    (hYd : ∀ d d' : ℕ → DemandVec n, (∀ r < t, d r = d' r) → Y d = Y d')
    (k : ℝ → (Fin m → DemandVec n) → ℝ≥0∞)
    (hk : Measurable fun p : ℝ × (Fin m → DemandVec n) => k p.1 p.2) :
    ∫⁻ z, (if E (padHist N' z) then k (Y (padHist N' z)) (fun j => padHist N' z (t + j)) else 0)
        ∂(Measure.pi fun _ : Fin N' => N.μ)
      = ∫⁻ z, (if E (padHist N' z) then ∫⁻ b, k (Y (padHist N' z)) b
          ∂(Measure.pi fun _ : Fin m => N.μ) else 0) ∂(Measure.pi fun _ : Fin N' => N.μ) := by
  set Φ : (ℕ → DemandVec n) → (Fin m → DemandVec n) → ℝ≥0∞ := fun d b =>
    if E d then k (Y d) b else 0 with hΦ
  have hΦm : Measurable fun p : (ℕ → DemandVec n) × (Fin m → DemandVec n) => Φ p.1 p.2 :=
    Measurable.ite (measurable_fst hE) (hk.comp ((hY.comp measurable_fst).prodMk measurable_snd))
      measurable_const
  have hΦd : ∀ (d d' : ℕ → DemandVec n) (b : Fin m → DemandVec n), (∀ s < t, d s = d' s) →
      Φ d b = Φ d' b := by
    intro d d' b h
    simp only [hΦ]
    by_cases h1 : E d
    · rw [if_pos h1, if_pos ((hEd d d' h).1 h1), hYd d d' h]
    · rw [if_neg h1, if_neg (fun h' => h1 ((hEd d d' h).2 h'))]
  have := lintegral_blk N.μ N' t m htm Φ hΦm hΦd
  simp only [hΦ] at this
  rw [this]
  refine lintegral_congr fun z => ?_
  split_ifs <;> simp

/-! ### Preparation and transient periods -/

lemma prep_bd (hN : N.Standing) : ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ T N' : ℕ, T ≤ N' →
    ∫⁻ z, ∑ t ∈ Finset.range T, (if act N x c (padHist N' z) t then 0
        else ENNReal.ofReal (1 + Dall (padHist N' z) t)) ∂(Measure.pi fun _ : Fin N' => N.μ) ≤ C := by
  obtain ⟨C, hC, h⟩ := fifo_prep_bound N.μ hN.mean_pos hN.mean_lt_top
    (N.Tpipe - 1 + max 1 (N.L c.sendTo) + 1) (fun i => IP N x c (fun _ => 0) 0 i - c.S i)
  refine ⟨C, hC, fun T N' hT => le_trans (lintegral_mono fun z =>
    Finset.sum_le_sum fun t _ => ?_) (h T N' hT)⟩
  have e : act N x c (padHist N' z) t ↔ (N.Tpipe - 1 + max 1 (N.L c.sendTo) + 1 ≤ t + 1 ∧
      ∀ i, IP N x c (fun _ => 0) 0 i - c.S i
        ≤ ∑ s ∈ Finset.range t, ((padHist N' z s i : ℝ≥0) : ℝ)) := by
    unfold act IP
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, fun i => by linarith [h2 i]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, fun i => by linarith [h2 i]⟩
  by_cases h1 : act N x c (padHist N' z) t
  · rw [if_pos h1]; exact zero_le
  · rw [if_neg h1]
    split_ifs with h2
    · exact absurd (e.2 h2) h1
    · exact le_rfl

lemma TI_bd (hN : N.Standing) : ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ T N' : ℕ, T + N.L0 + 1 ≤ N' →
    ∫⁻ z, ∑ t ∈ Finset.range T, (if TI N x c (padHist N' z) t then
        ENNReal.ofReal (1 + Dall (padHist N' z) t) else 0) ∂(Measure.pi fun _ : Fin N' => N.μ) ≤ C := by
  obtain ⟨Cp, hCp, hp⟩ := prep_bd N x c hN
  set m : ℝ≥0∞ := ∑ i, ∫⁻ a, (a i : ℝ≥0∞) ∂N.μ with hm
  have hmf : m ≠ ∞ := ENNReal.sum_ne_top.2 fun i _ => (hN.mean_lt_top i).ne
  have hL : ((N.L0 + 1 : ℕ) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  refine ⟨(N.L0 + 1 : ℕ) * (1 + (N.L0 + 1 : ℕ) * m) + Cp + (N.L0 + 1 : ℕ) * m * Cp, ?_,
    fun T N' hT => ?_⟩
  · refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hL
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top hL hmf⟩), hCp⟩,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top hL hmf) hCp⟩
  have hD := measurable_padHist' (α := DemandVec n) N'
  set W : (ℕ → DemandVec n) → ℕ → ℝ := fun d t => ∑ j : Fin (N.L0 + 1), ∑ i, ((d (t + j) i : ℝ≥0) : ℝ)
    with hW
  -- pathwise
  have hpath : ∀ d : ℕ → DemandVec n, ∑ t ∈ Finset.range T, (if TI N x c d t then
        ENNReal.ofReal (1 + Dall d t) else 0)
      ≤ ∑ t ∈ Finset.range (N.L0 + 1), ENNReal.ofReal (1 + Dall d t)
        + (∑ t ∈ Finset.range T, (if act N x c d t then 0 else ENNReal.ofReal (1 + Dall d t))
          + ∑ t ∈ Finset.range T, (if act N x c d t then 0 else ENNReal.ofReal (W d t))) := by
    intro d
    calc ∑ t ∈ Finset.range T, (if TI N x c d t then ENNReal.ofReal (1 + Dall d t) else 0)
        ≤ ∑ t ∈ Finset.range (N.L0 + 1 + T),
            (if TI N x c d t then ENNReal.ofReal (1 + Dall d t) else 0) :=
          Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
      _ = ∑ t ∈ Finset.range (N.L0 + 1), (if TI N x c d t then ENNReal.ofReal (1 + Dall d t) else 0)
          + ∑ t ∈ Finset.range T, (if TI N x c d (N.L0 + 1 + t) then
              ENNReal.ofReal (1 + Dall d (N.L0 + 1 + t)) else 0) := Finset.sum_range_add _ _ _
      _ ≤ _ := by
        refine add_le_add (Finset.sum_le_sum fun t _ => ?_) ?_
        · split_ifs <;> simp
        · rw [← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun t _ => ?_
          have eTI : TI N x c d (N.L0 + 1 + t) ↔ ¬ act N x c d t := by
            unfold TI
            rw [show N.L0 + 1 + t - N.L0 - 1 = t by omega]
            constructor
            · intro h ha; exact h ⟨by omega, ha⟩
            · intro h h'; exact h h'.2
          by_cases ha : act N x c d t
          · rw [if_neg (fun h => (eTI.1 h) ha), if_pos ha, if_pos ha, add_zero]
          · rw [if_pos (eTI.2 ha), if_neg ha, if_neg ha]
            have hW0 : 0 ≤ W d t := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ =>
              NNReal.coe_nonneg _
            rw [← ENNReal.ofReal_add (by linarith [Dall_nonneg d t]) hW0]
            refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
            simp only [hW]
            unfold Dall
            rw [show N.L0 + 1 + t = t + (N.L0 + 1) by omega]
            have e4 : ∀ i : Fin n, ∑ s ∈ Finset.range (t + (N.L0 + 1)), ((d s i : ℝ≥0) : ℝ)
                = ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ)
                  + ∑ j ∈ Finset.range (N.L0 + 1), ((d (t + j) i : ℝ≥0) : ℝ) := fun i =>
              Finset.sum_range_add _ _ _
            rw [Finset.sum_congr rfl fun i _ => e4 i, Finset.sum_add_distrib]
            have e3 : ∑ j : Fin (N.L0 + 1), ∑ i, ((d (t + j) i : ℝ≥0) : ℝ)
                = ∑ i, ∑ j ∈ Finset.range (N.L0 + 1), ((d (t + j) i : ℝ≥0) : ℝ) := by
              rw [Fin.sum_univ_eq_sum_range (fun j => ∑ i, ((d (t + j) i : ℝ≥0) : ℝ)) (N.L0 + 1),
                Finset.sum_comm]
            rw [e3]; ring
  -- measurability
  have hm1 : Measurable fun z : Fin N' → DemandVec n =>
      ∑ t ∈ Finset.range (N.L0 + 1), ENNReal.ofReal (1 + Dall (padHist N' z) t) :=
    Finset.measurable_sum _ fun t _ => ((measurable_const.add (Dall_meas t)).ennreal_ofReal).comp hD
  have hm2 : Measurable fun z : Fin N' → DemandVec n =>
      ∑ t ∈ Finset.range T, (if act N x c (padHist N' z) t then 0
        else ENNReal.ofReal (1 + Dall (padHist N' z) t)) :=
    Finset.measurable_sum _ fun t _ => (Measurable.ite (act_meas N x c t) measurable_const
      (measurable_const.add (Dall_meas t)).ennreal_ofReal).comp hD
  have hWm : ∀ t, Measurable fun d : ℕ → DemandVec n => W d t := fun t =>
    Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun i _ => meas_coord (t + j) i
  have hm3 : ∀ t ∈ Finset.range T, Measurable fun z : Fin N' → DemandVec n =>
      (if act N x c (padHist N' z) t then 0 else ENNReal.ofReal (W (padHist N' z) t)) := fun t _ =>
    (Measurable.ite (act_meas N x c t) measurable_const (hWm t).ennreal_ofReal).comp hD
  calc ∫⁻ z, ∑ t ∈ Finset.range T, (if TI N x c (padHist N' z) t then
        ENNReal.ofReal (1 + Dall (padHist N' z) t) else 0) ∂(Measure.pi fun _ : Fin N' => N.μ)
      ≤ ∫⁻ z, (∑ t ∈ Finset.range (N.L0 + 1), ENNReal.ofReal (1 + Dall (padHist N' z) t)
        + (∑ t ∈ Finset.range T, (if act N x c (padHist N' z) t then 0
            else ENNReal.ofReal (1 + Dall (padHist N' z) t))
          + ∑ t ∈ Finset.range T, (if act N x c (padHist N' z) t then 0
            else ENNReal.ofReal (W (padHist N' z) t)))) ∂(Measure.pi fun _ : Fin N' => N.μ) :=
        lintegral_mono fun z => hpath _
    _ = ∑ t ∈ Finset.range (N.L0 + 1), ∫⁻ z, ENNReal.ofReal (1 + Dall (padHist N' z) t)
            ∂(Measure.pi fun _ : Fin N' => N.μ)
        + (∫⁻ z, ∑ t ∈ Finset.range T, (if act N x c (padHist N' z) t then 0
            else ENNReal.ofReal (1 + Dall (padHist N' z) t)) ∂(Measure.pi fun _ : Fin N' => N.μ)
          + ∑ t ∈ Finset.range T, ∫⁻ z, (if act N x c (padHist N' z) t then 0
            else ENNReal.ofReal (W (padHist N' z) t)) ∂(Measure.pi fun _ : Fin N' => N.μ)) := by
        rw [lintegral_add_left hm1, lintegral_add_left hm2, lintegral_finsetSum _ hm3,
          lintegral_finsetSum (f := fun t z => ENNReal.ofReal (1 + Dall (padHist N' z) t)) _
            fun t _ => ((measurable_const.add (Dall_meas t)).ennreal_ofReal).comp hD]
    _ ≤ (N.L0 + 1 : ℕ) * (1 + (N.L0 + 1 : ℕ) * m) + (Cp + (N.L0 + 1 : ℕ) * m * Cp) := by
        refine add_le_add ?_ (add_le_add (hp T N' (by omega)) ?_)
        · calc ∑ t ∈ Finset.range (N.L0 + 1), ∫⁻ z, ENNReal.ofReal (1 + Dall (padHist N' z) t)
                ∂(Measure.pi fun _ : Fin N' => N.μ)
              ≤ ∑ _t ∈ Finset.range (N.L0 + 1), (1 + (N.L0 + 1 : ℕ) * m) :=
                Finset.sum_le_sum fun t ht => (lin_exp N N' t).trans (by
                  gcongr; exact_mod_cast (Finset.mem_range.1 ht).le)
            _ = (N.L0 + 1 : ℕ) * (1 + (N.L0 + 1 : ℕ) * m) := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        · -- the window terms
          have hblk : ∀ t ∈ Finset.range T, ∫⁻ z, (if act N x c (padHist N' z) t then 0
              else ENNReal.ofReal (W (padHist N' z) t)) ∂(Measure.pi fun _ : Fin N' => N.μ)
              ≤ (N.L0 + 1 : ℕ) * m * ∫⁻ z, (if act N x c (padHist N' z) t then 0
                else ENNReal.ofReal (1 + Dall (padHist N' z) t)) ∂(Measure.pi fun _ : Fin N' => N.μ) := by
            intro t ht
            have htT : t + (N.L0 + 1) ≤ N' := by simp at ht; omega
            have e1 := blk_ind N N' t (N.L0 + 1) htT (fun d => ¬ act N x c d t)
              (act_meas N x c t).compl (fun d d' h => not_congr (act_dep N x c t d d' h))
              (fun _ => 0) measurable_const (fun _ _ _ => rfl)
              (fun _ b => ENNReal.ofReal (∑ j, ∑ i, ((b j i : ℝ≥0) : ℝ)))
              ((Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun i _ =>
                ((measurable_pi_apply i).comp ((measurable_pi_apply j).comp measurable_snd)).coe_nnreal_real).ennreal_ofReal)
            have e2 : ∀ z : Fin N' → DemandVec n, (if act N x c (padHist N' z) t then 0
                else ENNReal.ofReal (W (padHist N' z) t))
                = (if ¬ act N x c (padHist N' z) t then
                  ENNReal.ofReal (∑ j : Fin (N.L0 + 1), ∑ i, ((padHist N' z (t + j) i : ℝ≥0) : ℝ))
                  else 0) := fun z => by
              by_cases ha : act N x c (padHist N' z) t
              · rw [if_pos ha, if_neg (not_not.2 ha)]
              · rw [if_neg ha, if_pos ha]
            simp_rw [e2]
            rw [e1, ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top hL hmf)]
            refine lintegral_mono fun z => ?_
            rw [ker_sum N (N.L0 + 1)]
            by_cases ha : act N x c (padHist N' z) t
            · rw [if_neg (not_not.2 ha), if_pos ha, mul_zero]
            · rw [if_pos ha, if_neg ha]
              calc ((N.L0 + 1 : ℕ) : ℝ≥0∞) * ∑ i, ∫⁻ a, (a i : ℝ≥0∞) ∂N.μ
                  = (N.L0 + 1 : ℕ) * m * 1 := by rw [mul_one]
                _ ≤ (N.L0 + 1 : ℕ) * m * ENNReal.ofReal (1 + Dall (padHist N' z) t) := by
                  gcongr
                  rw [← ENNReal.ofReal_one]
                  exact ENNReal.ofReal_le_ofReal (by linarith [Dall_nonneg (padHist N' z) t])
          calc ∑ t ∈ Finset.range T, ∫⁻ z, (if act N x c (padHist N' z) t then 0
                else ENNReal.ofReal (W (padHist N' z) t)) ∂(Measure.pi fun _ : Fin N' => N.μ)
              ≤ ∑ t ∈ Finset.range T, (N.L0 + 1 : ℕ) * m * ∫⁻ z, (if act N x c (padHist N' z) t then 0
                else ENNReal.ofReal (1 + Dall (padHist N' z) t)) ∂(Measure.pi fun _ : Fin N' => N.μ) :=
                Finset.sum_le_sum hblk
            _ = (N.L0 + 1 : ℕ) * m * ∑ t ∈ Finset.range T, ∫⁻ z, (if act N x c (padHist N' z) t then 0
                else ENNReal.ofReal (1 + Dall (padHist N' z) t)) ∂(Measure.pi fun _ : Fin N' => N.μ) :=
                (Finset.mul_sum _ _ _).symm
            _ ≤ (N.L0 + 1 : ℕ) * m * Cp := by
                gcongr
                exact (sum_lintegral_le _ _ _).trans (hp T N' (by omega))
    _ = _ := by ring

end long

section long2

variable {n : ℕ} (N : Network n) (x : InitState n) (c : ConChoice n)

/-! ### `(s,S)` dynamics of the supplier and of the retailers -/

lemma sup_ss (hn : 0 < n) (hN : N.Standing) (hs0S : c.s0 ≤ c.S0) (f : ℝ → ℝ) (hfm : Measurable f)
    (hfb : ∀ a b : ℝ, ∃ C, ∀ y ∈ Set.Icc a b, f y ≤ C) (hf0 : ∀ y, 0 ≤ f y) (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ T N' : ℕ, T ≤ N' →
      ∫⁻ z, ∑ t ∈ Finset.range T, (if act N x c (padHist N' z) t then
          ENNReal.ofReal (K * (if 0 < q0 N x c (padHist N' z) t then 1 else 0)
            + f (Ypost N x c (padHist N' z) t)) else 0) ∂(Measure.pi fun _ : Fin N' => N.μ)
        ≤ T * ssAvgCost N.aggregate f K c.s0 c.S0 + C := by
  have hg : Measurable fun a : DemandVec n => ∑ i, a i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  obtain ⟨C, hC, h⟩ := ss_poisson_upper_meas N.μ (fun a => ∑ i, a i) hg N.aggregate rfl
    (mean_agg_pos hn N hN) f hfm hfb hf0 K c.s0 c.S0 0 hK hs0S
    (fun t d => act N x c d t) (fun t d => Yp N x c d t)
    (fun t => act_meas N x c t) (fun t => Yp_meas N x c t)
    (fun t d d' h => act_dep N x c t d d' h) (fun t d d' h => Yp_dep N x c t d d' h)
    (fun t d h => act_mono N x c d t h)
    (fun t d h => by
      have e : (act N x c d t ∧ Yp N x c d t ≤ c.s0) ↔ Yp N x c d t ≤ c.s0 :=
        ⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩
      show Yp N x c d (t + 1) = _
      rw [Yp_succ, NNReal.coe_sum]
      unfold Ypost
      simp only [e])
    (fun d h => absurd h (not_act_zero N x c d))
    (fun t d h1 h2 => by
      show Yp N x c d (t + 1) ≤ 0
      rw [Yp_prep N x c d (t + 1) (fun t' ht' ha' => h1 (act_mono' N x c d (by omega) ha'))]
      exact Finset.sum_nonpos fun i _ => sub_nonpos.2 (act_IP N x c d (t + 1) h2 i))
  have key : ∀ (d : ℕ → DemandVec n) (t : ℕ), (if act N x c d t then
      ENNReal.ofReal (K * (if 0 < q0 N x c d t then 1 else 0) + f (Ypost N x c d t)) else 0)
      = (if act N x c d t then ENNReal.ofReal (K * (if Yp N x c d t ≤ c.s0 ∧ Yp N x c d t < c.S0
          then 1 else 0) + f (if Yp N x c d t ≤ c.s0 then c.S0 else Yp N x c d t)) else 0) := by
    intro d t
    by_cases ha : act N x c d t
    · rw [if_pos ha, if_pos ha]
      by_cases hy : Yp N x c d t ≤ c.s0
      · have hq0 : q0 N x c d t = c.S0 - Yp N x c d t := by unfold q0; rw [if_pos ⟨ha, hy⟩]
        have hYp : Ypost N x c d t = c.S0 := by unfold Ypost; rw [if_pos ⟨ha, hy⟩]
        have e : (0 < c.S0 - Yp N x c d t) ↔ (Yp N x c d t ≤ c.s0 ∧ Yp N x c d t < c.S0) :=
          ⟨fun h => ⟨hy, by linarith⟩, fun h => by linarith [h.2]⟩
        rw [hq0, hYp, if_pos hy, if_congr e rfl rfl]
      · have hq0 : q0 N x c d t = 0 := by unfold q0; rw [if_neg (fun h' => hy h'.2)]
        have hYp : Ypost N x c d t = Yp N x c d t := by
          unfold Ypost; rw [if_neg (fun h' => hy h'.2)]
        rw [hq0, hYp, if_neg hy, if_neg (lt_irrefl 0), if_neg (fun h' => hy h'.1)]
    · rw [if_neg ha, if_neg ha]
  exact ⟨C, hC, fun T N' hT => le_trans (le_of_eq (lintegral_congr fun z =>
    Finset.sum_congr rfl fun t _ => key _ t)) (h T N' hT)⟩

lemma ret_ss (hN : N.Standing) (hsS : ∀ i, c.s i ≤ c.S i) (i : Fin n) (f : ℝ → ℝ)
    (hfm : Measurable f) (hfb : ∀ a b : ℝ, ∃ C, ∀ y ∈ Set.Icc a b, f y ≤ C) (hf0 : ∀ y, 0 ≤ f y)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ T N' : ℕ, T ≤ N' →
      ∫⁻ z, ∑ t ∈ Finset.range T, (if act N x c (padHist N' z) t then
          ENNReal.ofReal (K * (if Xpre N x c (padHist N' z) t i ≤ c.s i
              ∧ Xpre N x c (padHist N' z) t i < c.S i then 1 else 0)
            + f (Ph N x c (padHist N' z) t i)) else 0) ∂(Measure.pi fun _ : Fin N' => N.μ)
        ≤ T * ssAvgCost (N.marginal i) f K (c.s i) (c.S i) + C := by
  obtain ⟨C, hC, h⟩ := ss_poisson_upper_meas N.μ (fun a => a i) (measurable_pi_apply i)
    (N.marginal i) rfl (mean_marg_pos N hN i) f hfm hfb hf0 K (c.s i) (c.S i) (c.S i) hK (hsS i)
    (fun t d => act N x c d t) (fun t d => Xpre N x c d t i)
    (fun t => act_meas N x c t) (fun t => Xpre_meas N x c t i)
    (fun t d d' h => act_dep N x c t d d' h) (fun t d d' h => Xpre_dep N x c t d d' h i)
    (fun t d h => act_mono N x c d t h)
    (fun t d h => by
      show Xpre N x c d (t + 1) i = _
      have e1 : Xpre N x c d (t + 1) i = Ph N x c d t i - ((d t i : ℝ≥0) : ℝ) := by
        unfold Xpre
        rw [if_pos ⟨Nat.succ_pos t, by simpa using h⟩]
        simp
      rw [e1, Xpre_post N x c d t h i])
    (fun d h => absurd h (not_act_zero N x c d))
    (fun t d h1 h2 => by
      show Xpre N x c d (t + 1) i ≤ c.S i
      unfold Xpre
      rw [if_neg (fun h' => h1 (by simpa using h'.2))])
  have key : ∀ (d : ℕ → DemandVec n) (t : ℕ), (if act N x c d t then
      ENNReal.ofReal (K * (if Xpre N x c d t i ≤ c.s i ∧ Xpre N x c d t i < c.S i then 1 else 0)
        + f (Ph N x c d t i)) else 0)
      = (if act N x c d t then ENNReal.ofReal (K * (if Xpre N x c d t i ≤ c.s i
          ∧ Xpre N x c d t i < c.S i then 1 else 0)
          + f (if Xpre N x c d t i ≤ c.s i then c.S i else Xpre N x c d t i)) else 0) := by
    intro d t
    by_cases ha : act N x c d t
    · rw [if_pos ha, if_pos ha, Xpre_post N x c d t ha i]
    · rw [if_neg ha, if_neg ha]
  exact ⟨C, hC, fun T N' hT => le_trans (le_of_eq (lintegral_congr fun z =>
    Finset.sum_congr rfl fun t _ => key _ t)) (h T N' hT)⟩

lemma window_fin (d : ℕ → DemandVec n) (t m : ℕ) :
    ∑ j ∈ Finset.range m, ((∑ i, d (t + j) i : ℝ≥0) : ℝ)
      = ∑ j : Fin m, ((∑ i, d (t + j) i : ℝ≥0) : ℝ) :=
  (Fin.sum_univ_eq_sum_range (fun j => ((∑ i, d (t + j) i : ℝ≥0) : ℝ)) m).symm

lemma meas_wsum (m : ℕ) : Measurable fun p : ℝ × (Fin m → DemandVec n) =>
    ∑ j, ((∑ i, p.2 j i : ℝ≥0) : ℝ) :=
  Finset.measurable_sum _ fun j _ => (Finset.measurable_sum _ fun i _ =>
    (measurable_pi_apply i).comp ((measurable_pi_apply j).comp measurable_snd)).coe_nnreal_real

lemma meas_window (t m : ℕ) : Measurable fun d : ℕ → DemandVec n =>
    ∑ j ∈ Finset.range m, ((∑ i, d (t + j) i : ℝ≥0) : ℝ) :=
  Finset.measurable_sum _ fun j _ => (Finset.measurable_sum _ fun i _ =>
    (measurable_pi_apply i).comp (measurable_pi_apply (t + j))).coe_nnreal_real

/-! ### The supplier -/

/-- Supplier part of the per-period cost. -/
def supT (d : ℕ → DemandVec n) (t : ℕ) : ℝ :=
  (if act N x c d t then N.K0 * (if 0 < q0 N x c d t then 1 else 0) else 0)
  + (if N.L0 ≤ t ∧ act N x c d (t - N.L0) then
      whLoss N.h N.p (Ypost N x c d (t - N.L0)
        - ∑ j ∈ Finset.range N.L0, ((∑ i, d (t - N.L0 + j) i : ℝ≥0) : ℝ)) else 0)

lemma sup_long (hn : 0 < n) (hN : N.Standing) (hs0S : c.s0 ≤ c.S0) :
    LR (fun T => ∫⁻ z, ∑ t ∈ Finset.range T, ENNReal.ofReal (supT N x c (padHist (T + Mh N) z) t)
      ∂(Measure.pi fun _ : Fin (T + Mh N) => N.μ)) (ssAvgCost N.aggregate N.fL0 N.K0 c.s0 c.S0) := by
  have hh := hN.h_pos.le; have hp := hN.p_pos.le
  obtain ⟨C, hC, hss⟩ := sup_ss N x c hn hN hs0S N.fL0 (fL0_cont N hN).measurable
    (fun a b => ⟨N.fL0 a + (N.h + N.p) * (b - a), fun y hy => by
      have h1 := fL0_lip N hN y a
      rw [abs_of_nonneg (by linarith [hy.1] : (0:ℝ) ≤ y - a)] at h1
      have h2 := (abs_le.1 h1).2
      have h3 : (N.h + N.p) * (y - a) ≤ (N.h + N.p) * (b - a) :=
        mul_le_mul_of_nonneg_left (by linarith [hy.2]) (by linarith)
      linarith⟩)
    (fL0_nonneg N hN) N.K0 hN.K0_nonneg
  refine ⟨C, hC, fun T => ?_⟩
  set N' := T + Mh N with hN'
  have hD := measurable_padHist' (α := DemandVec n) N'
  set a : (ℕ → DemandVec n) → ℕ → ℝ≥0∞ := fun d t => if act N x c d t then
    ENNReal.ofReal (N.K0 * (if 0 < q0 N x c d t then 1 else 0)) else 0 with ha
  set B : (ℕ → DemandVec n) → ℕ → ℝ≥0∞ := fun d t => if act N x c d t then
    ENNReal.ofReal (whLoss N.h N.p (Ypost N x c d t
      - ∑ j ∈ Finset.range N.L0, ((∑ i, d (t + j) i : ℝ≥0) : ℝ))) else 0 with hB
  set B' : (ℕ → DemandVec n) → ℕ → ℝ≥0∞ := fun d t => if act N x c d t then
    ENNReal.ofReal (N.fL0 (Ypost N x c d t)) else 0 with hB'
  have hpath : ∀ d : ℕ → DemandVec n, ∑ t ∈ Finset.range T, ENNReal.ofReal (supT N x c d t)
      ≤ ∑ t ∈ Finset.range T, a d t + ∑ t ∈ Finset.range T, B d t := by
    intro d
    have h1 : ∀ t, ENNReal.ofReal (supT N x c d t) ≤ a d t + (if N.L0 ≤ t then B d (t - N.L0) else 0) := by
      intro t
      unfold supT
      refine ENNReal.ofReal_add_le.trans (add_le_add ?_ ?_)
      · simp only [ha]; split_ifs <;> simp
      · by_cases hL : N.L0 ≤ t
        · rw [if_pos hL]
          simp only [hB]
          by_cases hA : act N x c d (t - N.L0)
          · rw [if_pos ⟨hL, hA⟩, if_pos hA]
          · rw [if_neg (fun h => hA h.2), if_neg hA, ENNReal.ofReal_zero]
        · rw [if_neg (fun h => hL h.1), if_neg hL, ENNReal.ofReal_zero]
    calc ∑ t ∈ Finset.range T, ENNReal.ofReal (supT N x c d t)
        ≤ ∑ t ∈ Finset.range T, (a d t + (if N.L0 ≤ t then B d (t - N.L0) else 0)) :=
          Finset.sum_le_sum fun t _ => h1 t
      _ = ∑ t ∈ Finset.range T, a d t + ∑ t ∈ Finset.range T,
            (if N.L0 ≤ t then B d (t - N.L0) else 0) := Finset.sum_add_distrib
      _ ≤ _ := add_le_add le_rfl (shift_le (B d) T N.L0)
  have ham : Measurable fun d : ℕ → DemandVec n => ∑ t ∈ Finset.range T, a d t :=
    Finset.measurable_sum _ fun t _ => Measurable.ite (act_meas N x c t)
      (measurable_const.mul (Measurable.ite (measurableSet_lt measurable_const (q0_meas N x c t))
        measurable_const measurable_const)).ennreal_ofReal measurable_const
  have hBm : ∀ t, Measurable fun d : ℕ → DemandVec n => B d t := fun t =>
    Measurable.ite (act_meas N x c t) ((meas_whLoss N.h N.p).comp
      ((Ypost_meas N x c t).sub (meas_window t N.L0))).ennreal_ofReal measurable_const
  have hblk : ∀ t ∈ Finset.range T, ∫⁻ z, B (padHist N' z) t ∂(Measure.pi fun _ : Fin N' => N.μ)
      = ∫⁻ z, B' (padHist N' z) t ∂(Measure.pi fun _ : Fin N' => N.μ) := by
    intro t ht
    have htN : t + N.L0 ≤ N' := by simp at ht; simp only [hN', Mh]; omega
    have e1 := blk_ind N N' t N.L0 htN (fun d => act N x c d t) (act_meas N x c t)
      (fun d d' h => act_dep N x c t d d' h) (fun d => Ypost N x c d t) (Ypost_meas N x c t)
      (fun d d' h => Ypost_dep N x c t d d' h)
      (fun y b => ENNReal.ofReal (whLoss N.h N.p (y - ∑ j, ((∑ i, b j i : ℝ≥0) : ℝ))))
      ((meas_whLoss N.h N.p).comp (measurable_fst.sub (meas_wsum N.L0))).ennreal_ofReal
    have e2 : ∀ z : Fin N' → DemandVec n, B (padHist N' z) t
        = (if act N x c (padHist N' z) t then ENNReal.ofReal (whLoss N.h N.p
            (Ypost N x c (padHist N' z) t
              - ∑ j : Fin N.L0, ((∑ i, padHist N' z (t + j) i : ℝ≥0) : ℝ))) else 0) := fun z => by
      simp only [hB, window_fin]
    simp_rw [e2]
    rw [e1]
    refine lintegral_congr fun z => ?_
    simp only [hB']
    split_ifs
    · exact ker_fL0 N hN _
    · rfl
  calc ∫⁻ z, ∑ t ∈ Finset.range T, ENNReal.ofReal (supT N x c (padHist N' z) t)
        ∂(Measure.pi fun _ : Fin N' => N.μ)
      ≤ ∫⁻ z, (∑ t ∈ Finset.range T, a (padHist N' z) t + ∑ t ∈ Finset.range T, B (padHist N' z) t)
          ∂(Measure.pi fun _ : Fin N' => N.μ) := lintegral_mono fun z => hpath _
    _ = ∫⁻ z, ∑ t ∈ Finset.range T, a (padHist N' z) t ∂(Measure.pi fun _ : Fin N' => N.μ)
          + ∑ t ∈ Finset.range T, ∫⁻ z, B (padHist N' z) t ∂(Measure.pi fun _ : Fin N' => N.μ) := by
        rw [lintegral_add_left (f := fun z => ∑ t ∈ Finset.range T, a (padHist N' z) t) (ham.comp hD),
          lintegral_finsetSum (f := fun t z => B (padHist N' z) t) _ fun t _ => (hBm t).comp hD]
    _ = ∫⁻ z, ∑ t ∈ Finset.range T, a (padHist N' z) t ∂(Measure.pi fun _ : Fin N' => N.μ)
          + ∑ t ∈ Finset.range T, ∫⁻ z, B' (padHist N' z) t ∂(Measure.pi fun _ : Fin N' => N.μ) := by
        rw [Finset.sum_congr rfl hblk]
    _ ≤ ∫⁻ z, (∑ t ∈ Finset.range T, a (padHist N' z) t + ∑ t ∈ Finset.range T, B' (padHist N' z) t)
          ∂(Measure.pi fun _ : Fin N' => N.μ) :=
        (add_le_add le_rfl (sum_lintegral_le _ _ _)).trans (le_lintegral_add _ _)
    _ = ∫⁻ z, ∑ t ∈ Finset.range T, (if act N x c (padHist N' z) t then
          ENNReal.ofReal (N.K0 * (if 0 < q0 N x c (padHist N' z) t then 1 else 0)
            + N.fL0 (Ypost N x c (padHist N' z) t)) else 0) ∂(Measure.pi fun _ : Fin N' => N.μ) := by
        refine lintegral_congr fun z => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun t _ => ?_
        simp only [ha, hB']
        by_cases hA : act N x c (padHist N' z) t
        · rw [if_pos hA, if_pos hA, if_pos hA, ENNReal.ofReal_add (mul_nonneg hN.K0_nonneg
            (by split_ifs <;> norm_num)) (fL0_nonneg N hN _)]
        · rw [if_neg hA, if_neg hA, if_neg hA, add_zero]
    _ ≤ T * ssAvgCost N.aggregate N.fL0 N.K0 c.s0 c.S0 + C := hss T N' (by simp only [hN', Mh]; omega)

end long2

end OWMR.Asm

end Part11

section Part12

/-! Assembly, part 12: the shortage count and the trigger and width terms. -/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open OWMR OWMR.S6


namespace OWMR.Asm

section trig

variable {n : ℕ} (N : Network n) (x : InitState n) (c : ConChoice n)

lemma Bp_meas (t : ℕ) : MeasurableSet {d : ℕ → DemandVec n | Bp N x c d t} := by
  have h1 : MeasurableSet {d : ℕ → DemandVec n | N.L0 ≤ t ∧ act N x c d (t - N.L0)} := by
    by_cases hL : N.L0 ≤ t
    · simp only [hL, true_and]; exact act_meas N x c (t - N.L0)
    · simp only [hL, false_and, Set.setOf_false]; exact MeasurableSet.empty
  have h2 : MeasurableSet {d : ℕ → DemandVec n | Ypost N x c d (t - N.L0)
      < ∑ j ∈ Finset.range N.L0, ((∑ i, d (t - N.L0 + j) i : ℝ≥0) : ℝ)} :=
    measurableSet_lt (Ypost_meas N x c _) (meas_window (t - N.L0) N.L0)
  have e : {d : ℕ → DemandVec n | Bp N x c d t}
      = ({d | N.L0 ≤ t ∧ act N x c d (t - N.L0)} ∩ {d | Ypost N x c d (t - N.L0)
          < ∑ j ∈ Finset.range N.L0, ((∑ i, d (t - N.L0 + j) i : ℝ≥0) : ℝ)})
        ∪ ({d | N.L0 ≤ t ∧ act N x c d (t - N.L0)}ᶜ ∩ {d | act N x c d t}) := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    unfold Bp
    split_ifs with h <;> tauto
  rw [e]
  exact (h1.inter h2).union (h1.compl.inter (act_meas N x c t))

lemma Vmax_meas (t : ℕ) : Measurable fun d : ℕ → DemandVec n => Vmax N c d t := by
  have hg : Measurable fun d : ℕ → DemandVec n => fun j : Fin N.L0 => DP c d (t - N.L0 + j) :=
    measurable_pi_lambda _ fun j => Finset.measurable_sum _ fun i _ =>
      (measurable_pi_apply i).comp (measurable_pi_apply (t - N.L0 + j))
  exact ((meas_sup N.L0).comp hg).coe_nnreal_real

lemma Bp_count (hn : 0 < n) (hN : N.Standing) (hs0S : c.s0 ≤ c.S0) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ T N' : ℕ, T + N.L0 + 1 ≤ N' →
      ∫⁻ z, ∑ t ∈ Finset.range T, (if Bp N x c (padHist N' z) t then (1 : ℝ≥0∞) else 0)
          ∂(Measure.pi fun _ : Fin N' => N.μ)
        ≤ T * ssAvgCost N.aggregate (gsh N) 0 c.s0 c.S0 + C := by
  obtain ⟨C1, hC1, h1⟩ := sup_ss N x c hn hN hs0S (gsh N) (gsh_anti N).measurable
    (fun a b => ⟨1, fun y _ => gsh_le_one N y⟩) (gsh_nonneg N) 0 le_rfl
  obtain ⟨C2, hC2, h2⟩ := TI_bd N x c hN
  refine ⟨C1 + C2, ENNReal.add_ne_top.2 ⟨hC1, hC2⟩, fun T N' hT => ?_⟩
  have hD := measurable_padHist' (α := DemandVec n) N'
  set S : (ℕ → DemandVec n) → ℕ → ℝ≥0∞ := fun d t => if act N x c d t then
    (if Ypost N x c d t < ∑ j ∈ Finset.range N.L0, ((∑ i, d (t + j) i : ℝ≥0) : ℝ) then 1 else 0)
    else 0 with hS
  set S' : (ℕ → DemandVec n) → ℕ → ℝ≥0∞ := fun d t => if act N x c d t then
    ENNReal.ofReal (gsh N (Ypost N x c d t)) else 0 with hS'
  set G : (ℕ → DemandVec n) → ℝ≥0∞ := fun d => ∑ t ∈ Finset.range T, (if TI N x c d t then
    ENNReal.ofReal (1 + Dall d t) else 0) with hG
  have hpath : ∀ d : ℕ → DemandVec n, ∑ t ∈ Finset.range T, (if Bp N x c d t then (1 : ℝ≥0∞) else 0)
      ≤ ∑ t ∈ Finset.range T, S d t + G d := by
    intro d
    have h1 : ∀ t, (if Bp N x c d t then (1 : ℝ≥0∞) else 0)
        ≤ (if N.L0 ≤ t then S d (t - N.L0) else 0)
          + (if TI N x c d t then ENNReal.ofReal (1 + Dall d t) else 0) := by
      intro t
      by_cases hb : Bp N x c d t
      · rw [if_pos hb]
        have hb' := hb
        unfold Bp at hb'
        split_ifs at hb' with hc
        · have : S d (t - N.L0) = 1 := by simp only [hS]; rw [if_pos hc.2, if_pos hb']
          rw [if_pos hc.1, this]; exact le_self_add
        · have hTI : TI N x c d t := fun h' => hc ⟨by omega, act_mono' N x c d (by omega) h'.2⟩
          rw [if_pos hTI]
          calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
            _ ≤ ENNReal.ofReal (1 + Dall d t) :=
                ENNReal.ofReal_le_ofReal (by linarith [Dall_nonneg d t])
            _ ≤ _ := le_add_self
      · rw [if_neg hb]; exact zero_le
    calc ∑ t ∈ Finset.range T, (if Bp N x c d t then (1 : ℝ≥0∞) else 0)
        ≤ ∑ t ∈ Finset.range T, ((if N.L0 ≤ t then S d (t - N.L0) else 0)
          + (if TI N x c d t then ENNReal.ofReal (1 + Dall d t) else 0)) :=
          Finset.sum_le_sum fun t _ => h1 t
      _ = ∑ t ∈ Finset.range T, (if N.L0 ≤ t then S d (t - N.L0) else 0) + G d :=
          Finset.sum_add_distrib
      _ ≤ _ := add_le_add (shift_le (S d) T N.L0) le_rfl
  have hSm : ∀ t, Measurable fun d : ℕ → DemandVec n => S d t := fun t =>
    Measurable.ite (act_meas N x c t) (Measurable.ite (measurableSet_lt (Ypost_meas N x c t)
      (meas_window t N.L0)) measurable_const measurable_const) measurable_const
  have hblk : ∀ t ∈ Finset.range T, ∫⁻ z, S (padHist N' z) t ∂(Measure.pi fun _ : Fin N' => N.μ)
      = ∫⁻ z, S' (padHist N' z) t ∂(Measure.pi fun _ : Fin N' => N.μ) := by
    intro t ht
    have htN : t + N.L0 ≤ N' := by simp at ht; omega
    have e1 := blk_ind N N' t N.L0 htN (fun d => act N x c d t) (act_meas N x c t)
      (fun d d' h => act_dep N x c t d d' h) (fun d => Ypost N x c d t) (Ypost_meas N x c t)
      (fun d d' h => Ypost_dep N x c t d d' h)
      (fun y b => if y < ∑ j, ((∑ i, b j i : ℝ≥0) : ℝ) then (1 : ℝ≥0∞) else 0)
      (Measurable.ite (measurableSet_lt measurable_fst (meas_wsum N.L0)) measurable_const
        measurable_const)
    have e2 : ∀ z : Fin N' → DemandVec n, S (padHist N' z) t
        = (if act N x c (padHist N' z) t then
            (if Ypost N x c (padHist N' z) t
              < ∑ j : Fin N.L0, ((∑ i, padHist N' z (t + j) i : ℝ≥0) : ℝ) then (1 : ℝ≥0∞) else 0)
            else 0) := fun z => by
      simp only [hS, window_fin]
    simp_rw [e2]
    rw [e1]
    refine lintegral_congr fun z => ?_
    simp only [hS']
    split_ifs
    · exact ker_sh N _
    · rfl
  calc ∫⁻ z, ∑ t ∈ Finset.range T, (if Bp N x c (padHist N' z) t then (1 : ℝ≥0∞) else 0)
        ∂(Measure.pi fun _ : Fin N' => N.μ)
      ≤ ∫⁻ z, (∑ t ∈ Finset.range T, S (padHist N' z) t + G (padHist N' z))
          ∂(Measure.pi fun _ : Fin N' => N.μ) := lintegral_mono fun z => hpath _
    _ = ∑ t ∈ Finset.range T, ∫⁻ z, S (padHist N' z) t ∂(Measure.pi fun _ : Fin N' => N.μ)
          + ∫⁻ z, G (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ) := by
        rw [lintegral_add_left (f := fun z => ∑ t ∈ Finset.range T, S (padHist N' z) t)
          ((Finset.measurable_sum _ fun t _ => hSm t).comp hD),
          lintegral_finsetSum (f := fun t z => S (padHist N' z) t) _ fun t _ => (hSm t).comp hD]
    _ = ∑ t ∈ Finset.range T, ∫⁻ z, S' (padHist N' z) t ∂(Measure.pi fun _ : Fin N' => N.μ)
          + ∫⁻ z, G (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ) := by
        rw [Finset.sum_congr rfl hblk]
    _ ≤ (T * ssAvgCost N.aggregate (gsh N) 0 c.s0 c.S0 + C1) + C2 := by
        refine add_le_add ((sum_lintegral_le _ _ _).trans (le_trans (le_of_eq ?_) (h1 T N' (by omega))))
          (h2 T N' hT)
        refine lintegral_congr fun z => Finset.sum_congr rfl fun t _ => ?_
        simp only [hS', zero_mul, zero_add]
    _ = _ := by rw [add_assoc]

lemma Vmax_exp (hN : N.Standing) (y : ℝ) (N' t : ℕ) (ht : t - N.L0 + N.L0 ≤ N') :
    ∫⁻ z, ENNReal.ofReal (max (Vmax N c (padHist N' z) t - y) 0) ∂(Measure.pi fun _ : Fin N' => N.μ)
      = ENNReal.ofReal (∫ w, max (((Finset.univ.sup w : ℝ≥0) : ℝ) - y) 0
          ∂(Measure.pi fun _ : Fin N.L0 => N.μ.map (fun a : DemandVec n => ∑ i ∈ bset c, a i))) := by
  have hk : Measurable fun p : ℝ × (Fin N.L0 → DemandVec n) => ENNReal.ofReal
      (max (((Finset.univ.sup fun j : Fin N.L0 => ∑ i ∈ bset c, p.2 j i : ℝ≥0) : ℝ) - y) 0) :=
    ((((meas_sup N.L0).comp (measurable_pi_lambda _ fun j => Finset.measurable_sum _ fun i _ =>
      (measurable_pi_apply i).comp ((measurable_pi_apply j).comp measurable_snd))).coe_nnreal_real.sub
        measurable_const).max measurable_const).ennreal_ofReal
  have e1 := blk_ind N N' (t - N.L0) N.L0 ht (fun _ => True) MeasurableSet.univ
    (fun _ _ _ => Iff.rfl) (fun _ => 0) measurable_const (fun _ _ _ => rfl)
    (fun _ b => ENNReal.ofReal
      (max (((Finset.univ.sup fun j : Fin N.L0 => ∑ i ∈ bset c, b j i : ℝ≥0) : ℝ) - y) 0)) hk
  have e2 : ∀ z : Fin N' → DemandVec n, ENNReal.ofReal (max (Vmax N c (padHist N' z) t - y) 0)
      = (if True then ENNReal.ofReal (max (((Finset.univ.sup fun j : Fin N.L0 =>
          ∑ i ∈ bset c, padHist N' z (t - N.L0 + j) i : ℝ≥0) : ℝ) - y) 0) else 0) := fun z => by
    rw [if_pos trivial]; rfl
  rw [lintegral_congr (μ := Measure.pi fun _ : Fin N' => N.μ) e2, e1]
  simp only [if_true]
  rw [ker_vmax N hN (bset c) y, lintegral_const, measure_univ, mul_one]

lemma psi_anti : Antitone psi := by
  intro u u' h
  unfold psi
  have h1 : max (1 - 4 * u' / 3) 0 ≤ max (1 - 4 * u / 3) 0 := max_le_max (by linarith) le_rfl
  have h2 : 0 ≤ max (1 - 4 * u' / 3) 0 := le_max_right _ _
  have h3 : max (1 - 4 * u' / 3) 0 ^ 2 ≤ max (1 - 4 * u / 3) 0 ^ 2 := pow_le_pow_left₀ h2 h1 2
  exact div_le_div_of_nonneg_right h3 (by norm_num)

lemma psi_meas : Measurable psi := psi_anti.measurable

lemma psiS_mono (S w : ℝ) (hw : 0 ≤ w) : Monotone fun y : ℝ => psi ((S - y) / w) := by
  intro y y' h
  exact psi_anti (div_le_div_of_nonneg_right (by linarith) hw)

/-- The per-period bound on the trigger and width terms. -/
lemma pp_pt (hN : N.Standing) (hw : ∀ i, c.batch i = true → c.s i < c.S i) (y : ℝ) (hy : 0 ≤ y)
    (d : ℕ → DemandVec n) (t : ℕ) :
    ENNReal.ofReal (pp N x c d t)
      ≤ ENNReal.ofReal ((N.h + N.p) * (3 / 8) * y) * (if Bp N x c d t then 1 else 0)
        + ENNReal.ofReal ((N.h + N.p) * (3 / 8)) * ENNReal.ofReal (max (Vmax N c d t - y) 0)
        + ∑ i ∈ bset c, min (ENNReal.ofReal ((N.h + N.p) * (3 / 8) * (c.S i - c.s i))
              * (if Bp N x c d t then 1 else 0))
            (ENNReal.ofReal ((N.h + N.p) * (c.S i - c.s i)) * (if act N x c d t then
              ENNReal.ofReal (psi ((c.S i - Ph N x c d t i) / (c.S i - c.s i))) else 0)) := by
  have hh := hN.h_pos; have hp := hN.p_pos
  have hq : 0 ≤ N.h + N.p := by linarith
  have hV0 : 0 ≤ Vmax N c d t := NNReal.coe_nonneg _
  have hwi : ∀ i ∈ bset c, 0 ≤ c.S i - c.s i := fun i hi =>
    sub_nonneg.2 (hw i (by simpa [bset] using hi)).le
  have hmin_nn : ∀ i ∈ bset c, 0 ≤ (N.h + N.p) * min (3 / 8 * (c.S i - c.s i)
      * (if Bp N x c d t then 1 else 0)) ((if act N x c d t then 1 else 0)
        * ((c.S i - c.s i) * psi ((c.S i - Ph N x c d t i) / (c.S i - c.s i)))) := by
    intro i hi
    have := hwi i hi
    have := psi_nonneg ((c.S i - Ph N x c d t i) / (c.S i - c.s i))
    refine mul_nonneg hq (le_min ?_ ?_) <;> split_ifs <;> positivity
  have e1 : pp N x c d t = (N.h + N.p) * (3 / 8 * Vmax N c d t * (if Bp N x c d t then 1 else 0))
      + ∑ i ∈ bset c, (N.h + N.p) * min (3 / 8 * (c.S i - c.s i) * (if Bp N x c d t then 1 else 0))
        ((if act N x c d t then 1 else 0)
          * ((c.S i - c.s i) * psi ((c.S i - Ph N x c d t i) / (c.S i - c.s i)))) := by
    unfold pp; rw [mul_add, Finset.mul_sum]
  have hfirst : ENNReal.ofReal ((N.h + N.p) * (3 / 8 * Vmax N c d t * (if Bp N x c d t then 1 else 0)))
      ≤ ENNReal.ofReal ((N.h + N.p) * (3 / 8) * y) * (if Bp N x c d t then 1 else 0)
        + ENNReal.ofReal ((N.h + N.p) * (3 / 8)) * ENNReal.ofReal (max (Vmax N c d t - y) 0) := by
    by_cases hb : Bp N x c d t
    · rw [if_pos hb, if_pos hb, mul_one, mul_one, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := le_max_left (Vmax N c d t - y) 0
      nlinarith
    · rw [if_neg hb, if_neg hb, mul_zero, mul_zero, ENNReal.ofReal_zero]; exact zero_le
  have heach : ∀ i ∈ bset c, ENNReal.ofReal ((N.h + N.p) * min (3 / 8 * (c.S i - c.s i)
        * (if Bp N x c d t then 1 else 0)) ((if act N x c d t then 1 else 0)
          * ((c.S i - c.s i) * psi ((c.S i - Ph N x c d t i) / (c.S i - c.s i)))))
      ≤ min (ENNReal.ofReal ((N.h + N.p) * (3 / 8) * (c.S i - c.s i))
              * (if Bp N x c d t then 1 else 0))
            (ENNReal.ofReal ((N.h + N.p) * (c.S i - c.s i)) * (if act N x c d t then
              ENNReal.ofReal (psi ((c.S i - Ph N x c d t i) / (c.S i - c.s i))) else 0)) := by
    intro i hi
    have hw0 := hwi i hi
    have hps := psi_nonneg ((c.S i - Ph N x c d t i) / (c.S i - c.s i))
    refine le_min ?_ ?_
    · refine (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (min_le_left _ _) hq)).trans ?_
      by_cases hb : Bp N x c d t
      · rw [if_pos hb, if_pos hb, mul_one, mul_one, mul_assoc]
      · rw [if_neg hb, if_neg hb, mul_zero, mul_zero, ENNReal.ofReal_zero]; exact zero_le
    · refine (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (min_le_right _ _) hq)).trans ?_
      by_cases ha : act N x c d t
      · rw [if_pos ha, if_pos ha, one_mul, ← mul_assoc, ENNReal.ofReal_mul (by positivity)]
      · rw [if_neg ha, if_neg ha, zero_mul, mul_zero, mul_zero, ENNReal.ofReal_zero]
  rw [e1]
  calc ENNReal.ofReal ((N.h + N.p) * (3 / 8 * Vmax N c d t * (if Bp N x c d t then 1 else 0))
        + ∑ i ∈ bset c, (N.h + N.p) * min (3 / 8 * (c.S i - c.s i) * (if Bp N x c d t then 1 else 0))
          ((if act N x c d t then 1 else 0)
            * ((c.S i - c.s i) * psi ((c.S i - Ph N x c d t i) / (c.S i - c.s i)))))
      ≤ ENNReal.ofReal ((N.h + N.p) * (3 / 8 * Vmax N c d t * (if Bp N x c d t then 1 else 0)))
        + ∑ i ∈ bset c, ENNReal.ofReal ((N.h + N.p) * min (3 / 8 * (c.S i - c.s i)
          * (if Bp N x c d t then 1 else 0)) ((if act N x c d t then 1 else 0)
            * ((c.S i - c.s i) * psi ((c.S i - Ph N x c d t i) / (c.S i - c.s i))))) := by
        refine ENNReal.ofReal_add_le.trans (le_of_eq ?_)
        rw [ENNReal.ofReal_sum_of_nonneg hmin_nn]
    _ ≤ _ := add_le_add hfirst (Finset.sum_le_sum heach)

end trig

section trig2

variable {n : ℕ} (N : Network n) (x : InitState n) (c : ConChoice n)

lemma min_mul_le (T a b : ℝ≥0∞) : min (T * a) (T * b) ≤ T * min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]; exact min_le_left _ _
  · rw [min_eq_right h]; exact min_le_right _ _

lemma pp_long (hn : 0 < n) (hN : N.Standing) (hsS : ∀ i, c.s i ≤ c.S i) (hs0S : c.s0 ≤ c.S0)
    (hw : ∀ i, c.batch i = true → c.s i < c.S i) (y : ℝ) (hy : 0 ≤ y)
    (hα : ssAvgCost N.aggregate (gsh N) 0 c.s0 c.S0 ≤ ENNReal.ofReal (N.h / (N.h + N.p))) :
    LR (fun T => ∫⁻ z, ENNReal.ofReal (∑ t ∈ Finset.range (T + N.L0),
          pp N x c (padHist (T + Mh N) z) t) ∂(Measure.pi fun _ : Fin (T + Mh N) => N.μ))
      (ENNReal.ofReal (3 / 8 * N.h * y)
        + ENNReal.ofReal ((N.h + N.p) * (3 / 8)) * ENNReal.ofReal (∫ w,
            max (((Finset.univ.sup w : ℝ≥0) : ℝ) - y) 0
            ∂(Measure.pi fun _ : Fin N.L0 => N.μ.map (fun a : DemandVec n => ∑ i ∈ bset c, a i)))
        + ∑ i ∈ bset c, min (ENNReal.ofReal (N.h * (3 / 8) * (c.S i - c.s i)))
            (ENNReal.ofReal ((N.h + N.p) * (c.S i - c.s i))
              * ssAvgCost (N.marginal i) (fun y => psi ((c.S i - y) / (c.S i - c.s i))) 0
                (c.s i) (c.S i))) := by
  have hh := hN.h_pos; have hp := hN.p_pos
  obtain ⟨CB, hCB, hBc⟩ := Bp_count N x c hn hN hs0S
  have hpsi : ∀ i, ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ T N' : ℕ, T ≤ N' →
      ∫⁻ z, ∑ t ∈ Finset.range T, (if act N x c (padHist N' z) t then
          ENNReal.ofReal (0 * (if Xpre N x c (padHist N' z) t i ≤ c.s i
              ∧ Xpre N x c (padHist N' z) t i < c.S i then 1 else 0)
            + psi ((c.S i - Ph N x c (padHist N' z) t i) / (c.S i - c.s i))) else 0)
          ∂(Measure.pi fun _ : Fin N' => N.μ)
        ≤ T * ssAvgCost (N.marginal i) (fun y => psi ((c.S i - y) / (c.S i - c.s i))) 0
            (c.s i) (c.S i) + C :=
    fun i => ret_ss N x c hN hsS i (fun y => psi ((c.S i - y) / (c.S i - c.s i)))
      (psi_meas.comp ((measurable_const.sub measurable_id).div_const _))
      (fun a b => ⟨psi ((c.S i - b) / (c.S i - c.s i)), fun y hy =>
        psiS_mono _ _ (sub_nonneg.2 (hsS i)) hy.2⟩)
      (fun y => psi_nonneg _) 0 le_rfl
  choose CI hCIf hCI using hpsi
  set α := ssAvgCost N.aggregate (gsh N) 0 c.s0 c.S0 with hαdef
  set I := ∫ w, max (((Finset.univ.sup w : ℝ≥0) : ℝ) - y) 0
    ∂(Measure.pi fun _ : Fin N.L0 => N.μ.map (fun a : DemandVec n => ∑ i ∈ bset c, a i)) with hI
  set ss : Fin n → ℝ≥0∞ := fun i => ssAvgCost (N.marginal i)
    (fun y => psi ((c.S i - y) / (c.S i - c.s i))) 0 (c.s i) (c.S i) with hss
  set c1 := ENNReal.ofReal ((N.h + N.p) * (3 / 8) * y) with hc1
  set c2 := ENNReal.ofReal ((N.h + N.p) * (3 / 8)) with hc2
  set c3 : Fin n → ℝ≥0∞ := fun i => ENNReal.ofReal ((N.h + N.p) * (3 / 8) * (c.S i - c.s i))
    with hc3
  set c4 : Fin n → ℝ≥0∞ := fun i => ENNReal.ofReal ((N.h + N.p) * (c.S i - c.s i)) with hc4
  set R0 := c1 * α + c2 * ENNReal.ofReal I + ∑ i ∈ bset c, min (c3 i * α) (c4 i * ss i) with hR0
  have hαf : α ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hα
  have hR0f : R0 ≠ ∞ := by
    refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hαf,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩, ENNReal.sum_ne_top.2 fun i _ =>
        ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hαf) (min_le_left _ _)⟩
  have hRle : R0 ≤ ENNReal.ofReal (3 / 8 * N.h * y) + c2 * ENNReal.ofReal I
      + ∑ i ∈ bset c, min (ENNReal.ofReal (N.h * (3 / 8) * (c.S i - c.s i))) (c4 i * ss i) := by
    have k1 : c1 * α ≤ ENNReal.ofReal (3 / 8 * N.h * y) := by
      calc c1 * α ≤ c1 * ENNReal.ofReal (N.h / (N.h + N.p)) := by gcongr
        _ = ENNReal.ofReal ((N.h + N.p) * (3 / 8) * y * (N.h / (N.h + N.p))) :=
            (ENNReal.ofReal_mul (by positivity)).symm
        _ = ENNReal.ofReal (3 / 8 * N.h * y) := by
            congr 1; field_simp
    have k3 : ∀ i ∈ bset c, c3 i * α ≤ ENNReal.ofReal (N.h * (3 / 8) * (c.S i - c.s i)) := by
      intro i hi
      have hw0 : 0 ≤ c.S i - c.s i := sub_nonneg.2 (hsS i)
      calc c3 i * α ≤ c3 i * ENNReal.ofReal (N.h / (N.h + N.p)) := by gcongr
        _ = ENNReal.ofReal ((N.h + N.p) * (3 / 8) * (c.S i - c.s i) * (N.h / (N.h + N.p))) :=
            (ENNReal.ofReal_mul (by positivity)).symm
        _ = ENNReal.ofReal (N.h * (3 / 8) * (c.S i - c.s i)) := by
            congr 1; field_simp
    exact add_le_add (add_le_add k1 le_rfl) (Finset.sum_le_sum fun i hi => min_le_min (k3 i hi) le_rfl)
  set C0 := c1 * CB + ∑ i ∈ bset c, (c3 i * CB + c4 i * CI i) with hC0
  have hC0f : C0 ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCB,
    ENNReal.sum_ne_top.2 fun i _ => ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCB,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hCIf i)⟩⟩
  refine (LR.shift N.L0 hR0f C0 hC0f fun T => ?_).rate hRle
  set T' := T + N.L0 with hT'
  set N' := T + Mh N with hN'
  have hLT := L0_le_Tpipe N
  have hT'N : T' ≤ N' := by simp only [hT', hN', Mh]; omega
  have hD := measurable_padHist' (α := DemandVec n) N'
  set NB : (ℕ → DemandVec n) → ℝ≥0∞ := fun d =>
    ∑ t ∈ Finset.range T', (if Bp N x c d t then 1 else 0) with hNB
  set VM : (ℕ → DemandVec n) → ℝ≥0∞ := fun d =>
    ∑ t ∈ Finset.range T', ENNReal.ofReal (max (Vmax N c d t - y) 0) with hVM
  set PS : Fin n → (ℕ → DemandVec n) → ℝ≥0∞ := fun i d => ∑ t ∈ Finset.range T',
    (if act N x c d t then ENNReal.ofReal (psi ((c.S i - Ph N x c d t i) / (c.S i - c.s i))) else 0)
    with hPS
  have hpath : ∀ d : ℕ → DemandVec n, ENNReal.ofReal (∑ t ∈ Finset.range T', pp N x c d t)
      ≤ c1 * NB d + c2 * VM d + ∑ i ∈ bset c, min (c3 i * NB d) (c4 i * PS i d) := by
    intro d
    rw [ENNReal.ofReal_sum_of_nonneg fun t _ => pp_nonneg N x c hN hw d t]
    have h1 := Finset.sum_le_sum fun t (_ : t ∈ Finset.range T') => pp_pt N x c hN hw y hy d t
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm] at h1
    refine h1.trans (add_le_add (add_le_add (le_of_eq ?_) (le_of_eq ?_))
      (Finset.sum_le_sum fun i _ => le_min ?_ ?_))
    · exact (Finset.mul_sum _ _ _).symm
    · exact (Finset.mul_sum _ _ _).symm
    · exact (Finset.sum_le_sum fun t _ => min_le_left _ _).trans (le_of_eq (Finset.mul_sum _ _ _).symm)
    · exact (Finset.sum_le_sum fun t _ => min_le_right _ _).trans (le_of_eq (Finset.mul_sum _ _ _).symm)
  have hNBm : Measurable NB := Finset.measurable_sum _ fun t _ =>
    Measurable.ite (Bp_meas N x c t) measurable_const measurable_const
  have hVMm : ∀ t, Measurable fun d : ℕ → DemandVec n => ENNReal.ofReal (max (Vmax N c d t - y) 0) :=
    fun t => (((Vmax_meas N c t).sub measurable_const).max measurable_const).ennreal_ofReal
  have hPSm : ∀ i, Measurable (PS i) := fun i => Finset.measurable_sum _ fun t _ =>
    Measurable.ite (act_meas N x c t) ((psi_meas.comp ((measurable_const.sub (Ph_meas N x c t i)).div_const
      _)).ennreal_ofReal) measurable_const
  have hENB : ∫⁻ z, NB (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ) ≤ T' * α + CB :=
    hBc T' N' (by simp only [hT', hN', Mh]; omega)
  have hEVM : ∫⁻ z, VM (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ) = T' * ENNReal.ofReal I := by
    simp only [hVM]
    rw [lintegral_finsetSum (f := fun t z => ENNReal.ofReal (max (Vmax N c (padHist N' z) t - y) 0)) _
      fun t _ => (hVMm t).comp hD]
    rw [Finset.sum_congr rfl fun t ht => Vmax_exp N c hN y N' t (by simp at ht; omega)]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hEPS : ∀ i, ∫⁻ z, PS i (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ) ≤ T' * ss i + CI i := by
    intro i
    refine le_trans (le_of_eq (lintegral_congr fun z => Finset.sum_congr rfl fun t _ => ?_))
      (hCI i T' N' hT'N)
    simp only [zero_mul, zero_add]
  calc ∫⁻ z, ENNReal.ofReal (∑ t ∈ Finset.range T', pp N x c (padHist N' z) t)
        ∂(Measure.pi fun _ : Fin N' => N.μ)
      ≤ ∫⁻ z, (c1 * NB (padHist N' z) + c2 * VM (padHist N' z)
          + ∑ i ∈ bset c, min (c3 i * NB (padHist N' z)) (c4 i * PS i (padHist N' z)))
          ∂(Measure.pi fun _ : Fin N' => N.μ) := lintegral_mono fun z => hpath _
    _ = c1 * ∫⁻ z, NB (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ)
          + c2 * ∫⁻ z, VM (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ)
          + ∑ i ∈ bset c, ∫⁻ z, min (c3 i * NB (padHist N' z)) (c4 i * PS i (padHist N' z))
              ∂(Measure.pi fun _ : Fin N' => N.μ) := by
        rw [lintegral_add_left (f := fun z => c1 * NB (padHist N' z) + c2 * VM (padHist N' z))
          ((measurable_const.mul (hNBm.comp hD)).add (measurable_const.mul
            ((Finset.measurable_sum _ fun t _ => hVMm t).comp hD))),
          lintegral_add_left (f := fun z => c1 * NB (padHist N' z))
            (measurable_const.mul (hNBm.comp hD)),
          lintegral_finsetSum (f := fun i z => min (c3 i * NB (padHist N' z)) (c4 i * PS i (padHist N' z)))
            _ fun i _ => (measurable_const.mul (hNBm.comp hD)).min
              (measurable_const.mul ((hPSm i).comp hD)),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ c1 * (T' * α + CB) + c2 * (T' * ENNReal.ofReal I)
          + ∑ i ∈ bset c, min (c3 i * (T' * α + CB)) (c4 i * (T' * ss i + CI i)) := by
        refine add_le_add (add_le_add (by gcongr) (le_of_eq (by rw [hEVM])))
          (Finset.sum_le_sum fun i _ => le_min ?_ ?_)
        · calc ∫⁻ z, min (c3 i * NB (padHist N' z)) (c4 i * PS i (padHist N' z))
                ∂(Measure.pi fun _ : Fin N' => N.μ)
              ≤ ∫⁻ z, c3 i * NB (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ) :=
                lintegral_mono fun z => min_le_left _ _
            _ = c3 i * ∫⁻ z, NB (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ) :=
                lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
            _ ≤ c3 i * (T' * α + CB) := by gcongr
        · calc ∫⁻ z, min (c3 i * NB (padHist N' z)) (c4 i * PS i (padHist N' z))
                ∂(Measure.pi fun _ : Fin N' => N.μ)
              ≤ ∫⁻ z, c4 i * PS i (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ) :=
                lintegral_mono fun z => min_le_right _ _
            _ = c4 i * ∫⁻ z, PS i (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ) :=
                lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
            _ ≤ c4 i * (T' * ss i + CI i) := by gcongr; exact hEPS i
    _ ≤ c1 * (T' * α + CB) + c2 * (T' * ENNReal.ofReal I)
          + ∑ i ∈ bset c, ((T' : ℝ≥0∞) * min (c3 i * α) (c4 i * ss i) + (c3 i * CB + c4 i * CI i)) := by
        refine add_le_add le_rfl (Finset.sum_le_sum fun i _ => ?_)
        calc min (c3 i * (T' * α + CB)) (c4 i * (T' * ss i + CI i))
            = min (T' * (c3 i * α) + c3 i * CB) (T' * (c4 i * ss i) + c4 i * CI i) := by
              congr 1 <;> ring
          _ ≤ min (T' * (c3 i * α)) (T' * (c4 i * ss i)) + c3 i * CB + c4 i * CI i := min_add_le' _ _ _ _
          _ ≤ T' * min (c3 i * α) (c4 i * ss i) + c3 i * CB + c4 i * CI i := by
              gcongr; exact min_mul_le _ _ _
          _ = _ := by rw [add_assoc]
    _ = ((T + N.L0 : ℕ) : ℝ≥0∞) * R0 + C0 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [hR0, hC0, hT']
        ring

end trig2

end OWMR.Asm

end Part12

section Part13

/-! Assembly, part 13: the retailer components and the initial terms. -/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open OWMR OWMR.S6


namespace OWMR.Asm

section ret

variable {n : ℕ} (N : Network n) (x : InitState n) (c : ConChoice n)

lemma F_lip (hN : N.Standing) (i : Fin n) (y y' : ℝ) :
    |N.F i y - N.F i y'| ≤ (N.H i + N.p) * |y - y'| := by
  rw [F_eq, F_eq]
  exact nv_lip _ _ (integrable_psum _ (integrable_marginal N hN i) _) _ _ (hN.H_pos i).le
    hN.p_pos.le y y'

lemma F_nonneg' (hN : N.Standing) (i : Fin n) (y : ℝ) : 0 ≤ N.F i y := by
  rw [F_eq]; exact nv_nonneg _ _ _ _ _ (hN.H_pos i).le hN.p_pos.le

lemma F_cont (hN : N.Standing) (i : Fin n) : Continuous (N.F i) := by
  have : N.F i = nvCost (Measure.pi fun _ : Fin (N.L i + 1) => N.marginal i)
      (fun w => ∑ j, (w j : ℝ)) (N.H i) N.p := funext fun y => F_eq N i y
  rw [this]
  exact nv_continuous _ _ (integrable_psum _ (integrable_marginal N hN i) _) _ _ (hN.H_pos i).le
    hN.p_pos.le

lemma cH_le_abs (hN : N.Standing) (i : Fin n) (y : ℝ) : cH N i y ≤ (N.H i + N.p) * |y| := by
  unfold cH
  have h1 : max y 0 ≤ |y| := max_le (le_abs_self y) (abs_nonneg y)
  have h2 : max (-y) 0 ≤ |y| := max_le (neg_le_abs y) (abs_nonneg y)
  nlinarith [mul_le_mul_of_nonneg_left h1 (hN.H_pos i).le, mul_le_mul_of_nonneg_left h2 hN.p_pos.le]

/-- The constant of the preparation positions. -/
def cF (i : Fin n) : ℝ :=
  N.F i 0 + (N.H i + N.p) * (|x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s| + |W0 N x| + 1)

lemma F_rPp (hN : N.Standing) (d : ℕ → DemandVec n) (t : ℕ) (i : Fin n) :
    N.F i (rPp N x c d t i) ≤ cF N x i * (1 + Dall d t) := by
  have hD := Dall_nonneg d t
  have hdi := dsum_le_Dall d t i
  have hdi0 : 0 ≤ ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) :=
    Finset.sum_nonneg fun s _ => NNReal.coe_nonneg _
  set A := |x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s| + |W0 N x| with hA
  have hA0 : 0 ≤ A := by positivity
  have habs : |rPp N x c d t i| ≤ A + Dall d t := by
    unfold rPp
    have hw : |(if N.Tpipe - 1 ≤ t ∧ i = c.sendTo then W0 N x else 0)| ≤ |W0 N x| := by
      split_ifs <;> simp
    calc |x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
          + (if N.Tpipe - 1 ≤ t ∧ i = c.sendTo then W0 N x else 0)
          - ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ)|
        ≤ |x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
          + (if N.Tpipe - 1 ≤ t ∧ i = c.sendTo then W0 N x else 0)|
          + |∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ)| := abs_sub _ _
      _ ≤ (|x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s|
          + |(if N.Tpipe - 1 ≤ t ∧ i = c.sendTo then W0 N x else 0)|)
          + |∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ)| := by gcongr; exact abs_add_le _ _
      _ ≤ A + Dall d t := by rw [abs_of_nonneg hdi0]; linarith
  have h1 := F_lip N hN i (rPp N x c d t i) 0
  rw [sub_zero] at h1
  have h2 : N.F i (rPp N x c d t i) ≤ N.F i 0 + (N.H i + N.p) * (A + Dall d t) := by
    have := (abs_le.1 h1).2
    have h3 : (N.H i + N.p) * |rPp N x c d t i| ≤ (N.H i + N.p) * (A + Dall d t) :=
      mul_le_mul_of_nonneg_left habs (by linarith [hN.H_pos i, hN.p_pos])
    linarith
  have hF0 := F_nonneg' N hN i 0
  have hHp : 0 ≤ N.H i + N.p := by linarith [hN.H_pos i, hN.p_pos]
  unfold cF
  rw [← hA]
  have h4 : (N.H i + N.p) * (A + Dall d t) ≤ (N.H i + N.p) * (A + 1) * (1 + Dall d t) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (by nlinarith) hHp
  nlinarith [mul_nonneg hF0 hD]

lemma cF_nonneg (hN : N.Standing) (i : Fin n) : 0 ≤ cF N x i := by
  unfold cF
  have := F_nonneg' N hN i 0
  have : 0 ≤ N.H i + N.p := by linarith [hN.H_pos i, hN.p_pos]
  positivity

/-- The physical retailer costs, reduced to the running positions. -/
lemma cH_part (hN : N.Standing) (i : Fin n) : ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ T : ℕ,
    ∫⁻ z, ∑ t ∈ Finset.range T, ENNReal.ofReal (cH N i (Pos' N x c (padHist (T + Mh N) z) t i
        - Dblk N (padHist (T + Mh N) z) t i)) ∂(Measure.pi fun _ : Fin (T + Mh N) => N.μ)
      ≤ ∫⁻ z, ∑ t ∈ Finset.range T, (if act N x c (padHist (T + Mh N) z) t then
          ENNReal.ofReal (N.F i (Ph N x c (padHist (T + Mh N) z) t i)) else 0)
          ∂(Measure.pi fun _ : Fin (T + Mh N) => N.μ) + C := by
  obtain ⟨Cp, hCp, hp⟩ := prep_bd N x c hN
  refine ⟨ENNReal.ofReal (cF N x i) * Cp, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCp, fun T => ?_⟩
  set N' := T + Mh N with hN'
  have hD := measurable_padHist' (α := DemandVec n) N'
  have hcH : Measurable fun y => cH N i y := by unfold cH; fun_prop
  have hm1 : ∀ t ∈ Finset.range T, Measurable fun z : Fin N' → DemandVec n =>
      ENNReal.ofReal (cH N i (Pos' N x c (padHist N' z) t i - Dblk N (padHist N' z) t i)) :=
    fun t _ => ((hcH.comp ((Pos'_meas N x c t i).sub (Dblk_meas N t i))).ennreal_ofReal).comp hD
  have hblk : ∀ t ∈ Finset.range T, ∫⁻ z, ENNReal.ofReal (cH N i (Pos' N x c (padHist N' z) t i
        - Dblk N (padHist N' z) t i)) ∂(Measure.pi fun _ : Fin N' => N.μ)
      = ∫⁻ z, ENNReal.ofReal (N.F i (Pos' N x c (padHist N' z) t i))
          ∂(Measure.pi fun _ : Fin N' => N.μ) := by
    intro t ht
    have htN : t + (N.L i + 1) ≤ N' := by
      have := L_le_Tpipe N i; simp at ht; simp only [hN', Mh]; omega
    have e1 := blk_ind N N' t (N.L i + 1) htN (fun _ => True) MeasurableSet.univ
      (fun _ _ _ => Iff.rfl) (fun d => Pos' N x c d t i) (Pos'_meas N x c t i)
      (fun d d' h => Pos'_dep N x c t d d' h i)
      (fun y b => ENNReal.ofReal (cH N i (y - ∑ j, ((b j i : ℝ≥0) : ℝ))))
      ((hcH.comp (measurable_fst.sub (Finset.measurable_sum _ fun j _ =>
        ((measurable_pi_apply i).comp ((measurable_pi_apply j).comp measurable_snd)).coe_nnreal_real))).ennreal_ofReal)
    have e2 : ∀ z : Fin N' → DemandVec n, ENNReal.ofReal (cH N i (Pos' N x c (padHist N' z) t i
        - Dblk N (padHist N' z) t i))
        = (if True then ENNReal.ofReal (cH N i (Pos' N x c (padHist N' z) t i
          - ∑ j : Fin (N.L i + 1), ((padHist N' z (t + j) i : ℝ≥0) : ℝ))) else 0) := fun z => by
      rw [if_pos trivial]
      unfold Dblk
      rw [Fin.sum_univ_eq_sum_range (fun j => ((padHist N' z (t + j) i : ℝ≥0) : ℝ)) (N.L i + 1)]
    rw [lintegral_congr (μ := Measure.pi fun _ : Fin N' => N.μ) e2, e1]
    refine lintegral_congr fun z => ?_
    rw [if_pos trivial]
    exact ker_F N hN i _
  have hpt : ∀ (d : ℕ → DemandVec n) (t : ℕ), ENNReal.ofReal (N.F i (Pos' N x c d t i))
      ≤ (if act N x c d t then ENNReal.ofReal (N.F i (Ph N x c d t i)) else 0)
        + ENNReal.ofReal (cF N x i) * (if act N x c d t then 0
          else ENNReal.ofReal (1 + Dall d t)) := by
    intro d t
    unfold Pos'
    by_cases ha : act N x c d t
    · rw [if_pos ha, if_pos ha, if_pos ha, mul_zero, add_zero]
    · rw [if_neg ha, if_neg ha, if_neg ha, zero_add, ← ENNReal.ofReal_mul (cF_nonneg N x hN i)]
      exact ENNReal.ofReal_le_ofReal (F_rPp N x c hN d t i)
  have hmF : Measurable fun z : Fin N' → DemandVec n => ∑ t ∈ Finset.range T,
      (if act N x c (padHist N' z) t then ENNReal.ofReal (N.F i (Ph N x c (padHist N' z) t i)) else 0) :=
    Finset.measurable_sum _ fun t _ => (Measurable.ite (act_meas N x c t)
      ((F_cont N hN i).measurable.comp (Ph_meas N x c t i)).ennreal_ofReal measurable_const).comp hD
  calc ∫⁻ z, ∑ t ∈ Finset.range T, ENNReal.ofReal (cH N i (Pos' N x c (padHist N' z) t i
        - Dblk N (padHist N' z) t i)) ∂(Measure.pi fun _ : Fin N' => N.μ)
      = ∑ t ∈ Finset.range T, ∫⁻ z, ENNReal.ofReal (N.F i (Pos' N x c (padHist N' z) t i))
          ∂(Measure.pi fun _ : Fin N' => N.μ) := by
        rw [lintegral_finsetSum _ hm1]; exact Finset.sum_congr rfl hblk
    _ ≤ ∫⁻ z, ∑ t ∈ Finset.range T, ENNReal.ofReal (N.F i (Pos' N x c (padHist N' z) t i))
          ∂(Measure.pi fun _ : Fin N' => N.μ) := sum_lintegral_le _ _ _
    _ ≤ ∫⁻ z, (∑ t ∈ Finset.range T, (if act N x c (padHist N' z) t then
          ENNReal.ofReal (N.F i (Ph N x c (padHist N' z) t i)) else 0)
          + ENNReal.ofReal (cF N x i) * ∑ t ∈ Finset.range T, (if act N x c (padHist N' z) t then 0
            else ENNReal.ofReal (1 + Dall (padHist N' z) t))) ∂(Measure.pi fun _ : Fin N' => N.μ) := by
        refine lintegral_mono fun z => ?_
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun t _ => hpt _ t
    _ = ∫⁻ z, ∑ t ∈ Finset.range T, (if act N x c (padHist N' z) t then
          ENNReal.ofReal (N.F i (Ph N x c (padHist N' z) t i)) else 0)
          ∂(Measure.pi fun _ : Fin N' => N.μ)
        + ENNReal.ofReal (cF N x i) * ∫⁻ z, ∑ t ∈ Finset.range T, (if act N x c (padHist N' z) t then 0
            else ENNReal.ofReal (1 + Dall (padHist N' z) t)) ∂(Measure.pi fun _ : Fin N' => N.μ) := by
        rw [lintegral_add_left hmF, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := by gcongr; exact hp T N' (by simp only [hN', Mh]; omega)

/-- Retailer part of the per-period cost. -/
def retT (d : ℕ → DemandVec n) (t : ℕ) (i : Fin n) : ℝ :=
  (if act N x c d t then N.h * (c.S i - Ph N x c d t i) else 0)
  + (if act N x c d t ∧ ¬ c.batch i = true then N.K i else 0)
  + cH N i (Pos' N x c d t i - Dblk N d t i)

lemma Ph_imm {i : Fin n} (hsi : c.s i = c.S i) (d : ℕ → DemandVec n) : ∀ t, Ph N x c d t i = c.S i
  | 0 => rfl
  | t + 1 => by
    have ih := Ph_imm hsi d t
    simp only [Ph]
    split_ifs with h1 h2
    · rfl
    · exfalso; apply h2; rw [ih, hsi]; linarith [NNReal.coe_nonneg (d t i)]
    · rfl

/-- The long-run cost of a retailer. -/
lemma ret_long (hN : N.Standing) (hsS : ∀ i, c.s i ≤ c.S i) (i : Fin n)
    (himm : ¬ c.batch i = true → c.s i = c.S i) :
    LR (fun T => ∫⁻ z, (∑ t ∈ Finset.range T, ENNReal.ofReal (retT N x c (padHist (T + Mh N) z) t i)
        + ∑ t ∈ Finset.range T, (if ord N x c (padHist (T + Mh N) z) t i then
            ENNReal.ofReal (7 / 3 * N.K i) else 0)) ∂(Measure.pi fun _ : Fin (T + Mh N) => N.μ))
      (if c.batch i = true then ssAvgCost (N.marginal i) (N.F i) (7 / 3 * N.K i) (c.s i) (c.S i)
          + ssAvgCost (N.marginal i) (fun y => N.h * max (c.S i - y) 0) 0 (c.s i) (c.S i)
        else ENNReal.ofReal (N.F i (c.S i) + N.K i)) := by
  have hh := hN.h_pos; have hK := hN.K_nonneg i
  obtain ⟨CH, hCH, hcHp⟩ := cH_part N x c hN i
  by_cases hb : c.batch i = true
  · rw [if_pos hb]
    obtain ⟨C1, hC1, h1⟩ := ret_ss N x c hN hsS i (N.F i) (F_cont N hN i).measurable
      (fun a b => ⟨N.F i a + (N.H i + N.p) * (b - a), fun y hy => by
        have h2 := F_lip N hN i y a
        rw [abs_of_nonneg (by linarith [hy.1] : (0:ℝ) ≤ y - a)] at h2
        have h3 := (abs_le.1 h2).2
        have h4 : (N.H i + N.p) * (y - a) ≤ (N.H i + N.p) * (b - a) :=
          mul_le_mul_of_nonneg_left (by linarith [hy.2]) (by linarith [hN.H_pos i, hN.p_pos])
        linarith⟩)
      (F_nonneg' N hN i) (7 / 3 * N.K i) (by positivity)
    obtain ⟨C2, hC2, h2⟩ := ret_ss N x c hN hsS i (fun y => N.h * max (c.S i - y) 0)
      (by fun_prop) (fun a b => ⟨N.h * max (c.S i - a) 0, fun y hy =>
        mul_le_mul_of_nonneg_left (max_le_max (by linarith [hy.1]) le_rfl) hh.le⟩)
      (fun y => mul_nonneg hh.le (le_max_right _ _)) 0 le_rfl
    refine ⟨C2 + (CH + C1), ENNReal.add_ne_top.2 ⟨hC2, ENNReal.add_ne_top.2 ⟨hCH, hC1⟩⟩,
      fun T => ?_⟩
    set N' := T + Mh N with hN'
    have hD := measurable_padHist' (α := DemandVec n) N'
    have hTN : T ≤ N' := by simp only [hN', Mh]; omega
    set Am : (ℕ → DemandVec n) → ℝ≥0∞ := fun d => ∑ t ∈ Finset.range T,
      (if act N x c d t then ENNReal.ofReal (N.h * (c.S i - Ph N x c d t i)) else 0) with hAm
    set Bm : (ℕ → DemandVec n) → ℝ≥0∞ := fun d => ∑ t ∈ Finset.range T,
      ENNReal.ofReal (cH N i (Pos' N x c d t i - Dblk N d t i)) with hBm
    set Om : (ℕ → DemandVec n) → ℝ≥0∞ := fun d => ∑ t ∈ Finset.range T,
      (if ord N x c d t i then ENNReal.ofReal (7 / 3 * N.K i) else 0) with hOm
    set Fm : (ℕ → DemandVec n) → ℝ≥0∞ := fun d => ∑ t ∈ Finset.range T,
      (if act N x c d t then ENNReal.ofReal (N.F i (Ph N x c d t i)) else 0) with hFm
    have hpath : ∀ d : ℕ → DemandVec n, ∑ t ∈ Finset.range T, ENNReal.ofReal (retT N x c d t i)
        + Om d ≤ Am d + Bm d + Om d := by
      intro d
      refine add_le_add ?_ le_rfl
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun t _ => ?_
      unfold retT
      rw [if_neg (show ¬ (act N x c d t ∧ ¬ c.batch i = true) from fun h => h.2 hb), add_zero]
      refine ENNReal.ofReal_add_le.trans (add_le_add ?_ le_rfl)
      split_ifs <;> simp
    have hFO : ∀ d : ℕ → DemandVec n, Fm d + Om d ≤ ∑ t ∈ Finset.range T, (if act N x c d t then
        ENNReal.ofReal (7 / 3 * N.K i * (if Xpre N x c d t i ≤ c.s i ∧ Xpre N x c d t i < c.S i
          then 1 else 0) + N.F i (Ph N x c d t i)) else 0) := by
      intro d
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun t _ => ?_
      have hF0 := F_nonneg' N hN i (Ph N x c d t i)
      by_cases ha : act N x c d t
      · rw [if_pos ha, if_pos ha]
        by_cases ho : ord N x c d t i
        · rw [if_pos ho, if_pos ((Xpre_order N x c hsS d t ha i).2 ⟨ho.1, ho.2.1, ho.2.2.1⟩),
            mul_one, ENNReal.ofReal_add (by positivity) hF0, add_comm]
        · rw [if_neg ho, add_zero]
          exact ENNReal.ofReal_le_ofReal (by
            have : 0 ≤ 7 / 3 * N.K i * (if Xpre N x c d t i ≤ c.s i ∧ Xpre N x c d t i < c.S i
              then (1 : ℝ) else 0) := by split_ifs <;> positivity
            linarith)
      · have ho : ¬ ord N x c d t i := fun ho => ha (act_mono' N x c d (by omega) ho.2.1)
        rw [if_neg ha, if_neg ho, if_neg ha, add_zero]
    have hAmm : Measurable Am := Finset.measurable_sum _ fun t _ => Measurable.ite (act_meas N x c t)
      (measurable_const.mul (measurable_const.sub (Ph_meas N x c t i))).ennreal_ofReal measurable_const
    have hcH : Measurable fun y => cH N i y := by unfold cH; fun_prop
    have hBmm : Measurable Bm := Finset.measurable_sum _ fun t _ =>
      (hcH.comp ((Pos'_meas N x c t i).sub (Dblk_meas N t i))).ennreal_ofReal
    have hEA : ∫⁻ z, Am (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ)
        ≤ T * ssAvgCost (N.marginal i) (fun y => N.h * max (c.S i - y) 0) 0 (c.s i) (c.S i) + C2 := by
      refine le_trans (le_of_eq (lintegral_congr fun z => Finset.sum_congr rfl fun t _ => ?_))
        (h2 T N' hTN)
      by_cases ha : act N x c (padHist N' z) t
      · rw [if_pos ha, if_pos ha, zero_mul, zero_add,
          max_eq_left (sub_nonneg.2 (Ph_bounds N x c hsS _ t i).2)]
      · rw [if_neg ha, if_neg ha]
    calc ∫⁻ z, (∑ t ∈ Finset.range T, ENNReal.ofReal (retT N x c (padHist N' z) t i)
          + Om (padHist N' z)) ∂(Measure.pi fun _ : Fin N' => N.μ)
        ≤ ∫⁻ z, (Am (padHist N' z) + Bm (padHist N' z) + Om (padHist N' z))
            ∂(Measure.pi fun _ : Fin N' => N.μ) := lintegral_mono fun z => hpath _
      _ = ∫⁻ z, Am (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ)
          + ∫⁻ z, Bm (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ)
          + ∫⁻ z, Om (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ) := by
          rw [lintegral_add_left (f := fun z => Am (padHist N' z) + Bm (padHist N' z))
            ((hAmm.comp hD).add (hBmm.comp hD)),
            lintegral_add_left (f := fun z => Am (padHist N' z)) (hAmm.comp hD)]
      _ ≤ ∫⁻ z, Am (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ)
          + (∫⁻ z, Fm (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ) + CH)
          + ∫⁻ z, Om (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ) := by
          gcongr; exact hcHp T
      _ ≤ ∫⁻ z, Am (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ)
          + (∫⁻ z, (Fm (padHist N' z) + Om (padHist N' z)) ∂(Measure.pi fun _ : Fin N' => N.μ) + CH) := by
          rw [add_assoc]
          refine add_le_add le_rfl ?_
          calc ∫⁻ z, Fm (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ) + CH
                + ∫⁻ z, Om (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ)
              = (∫⁻ z, Fm (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ)
                + ∫⁻ z, Om (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ)) + CH := by ring
            _ ≤ _ := add_le_add (le_lintegral_add _ _) le_rfl
      _ ≤ (T * ssAvgCost (N.marginal i) (fun y => N.h * max (c.S i - y) 0) 0 (c.s i) (c.S i) + C2)
          + ((T * ssAvgCost (N.marginal i) (N.F i) (7 / 3 * N.K i) (c.s i) (c.S i) + C1) + CH) := by
          refine add_le_add hEA (add_le_add ((lintegral_mono fun z => hFO _).trans (h1 T N' hTN)) le_rfl)
      _ = T * (ssAvgCost (N.marginal i) (N.F i) (7 / 3 * N.K i) (c.s i) (c.S i)
          + ssAvgCost (N.marginal i) (fun y => N.h * max (c.S i - y) 0) 0 (c.s i) (c.S i))
          + (C2 + (CH + C1)) := by ring
  · rw [if_neg hb]
    have hsi := himm hb
    refine ⟨CH, hCH, fun T => ?_⟩
    set N' := T + Mh N with hN'
    have hD := measurable_padHist' (α := DemandVec n) N'
    set Km : (ℕ → DemandVec n) → ℝ≥0∞ := fun d => ∑ t ∈ Finset.range T,
      (if act N x c d t then ENNReal.ofReal (N.K i) else 0) with hKm
    set Bm : (ℕ → DemandVec n) → ℝ≥0∞ := fun d => ∑ t ∈ Finset.range T,
      ENNReal.ofReal (cH N i (Pos' N x c d t i - Dblk N d t i)) with hBm
    set Fm : (ℕ → DemandVec n) → ℝ≥0∞ := fun d => ∑ t ∈ Finset.range T,
      (if act N x c d t then ENNReal.ofReal (N.F i (Ph N x c d t i)) else 0) with hFm
    have hpath : ∀ d : ℕ → DemandVec n, ∑ t ∈ Finset.range T, ENNReal.ofReal (retT N x c d t i)
        + ∑ t ∈ Finset.range T, (if ord N x c d t i then ENNReal.ofReal (7 / 3 * N.K i) else 0)
        ≤ Km d + Bm d := by
      intro d
      have hO : ∑ t ∈ Finset.range T, (if ord N x c d t i then ENNReal.ofReal (7 / 3 * N.K i) else 0)
          = 0 := Finset.sum_eq_zero fun t _ => if_neg (fun ho => hb ho.2.2.2)
      rw [hO, add_zero, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun t _ => ?_
      unfold retT
      rw [Ph_imm N x c hsi d t, sub_self, mul_zero, ite_self, zero_add]
      refine ENNReal.ofReal_add_le.trans (add_le_add ?_ le_rfl)
      by_cases ha : act N x c d t
      · rw [if_pos ⟨ha, hb⟩, if_pos ha]
      · rw [if_neg (fun h => ha h.1), if_neg ha, ENNReal.ofReal_zero]
    have hKmm : Measurable Km := Finset.measurable_sum _ fun t _ =>
      Measurable.ite (act_meas N x c t) measurable_const measurable_const
    have hKF : ∀ d : ℕ → DemandVec n, Km d + Fm d ≤ T * ENNReal.ofReal (N.F i (c.S i) + N.K i) := by
      intro d
      rw [← Finset.sum_add_distrib]
      calc ∑ t ∈ Finset.range T, ((if act N x c d t then ENNReal.ofReal (N.K i) else 0)
            + (if act N x c d t then ENNReal.ofReal (N.F i (Ph N x c d t i)) else 0))
          ≤ ∑ _t ∈ Finset.range T, ENNReal.ofReal (N.F i (c.S i) + N.K i) :=
            Finset.sum_le_sum fun t _ => by
              by_cases ha : act N x c d t
              · rw [if_pos ha, if_pos ha, Ph_imm N x c hsi d t,
                  ENNReal.ofReal_add (F_nonneg' N hN i _) hK, add_comm]
              · rw [if_neg ha, if_neg ha, add_zero]; exact zero_le
        _ = T * ENNReal.ofReal (N.F i (c.S i) + N.K i) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc ∫⁻ z, (∑ t ∈ Finset.range T, ENNReal.ofReal (retT N x c (padHist N' z) t i)
          + ∑ t ∈ Finset.range T, (if ord N x c (padHist N' z) t i then
            ENNReal.ofReal (7 / 3 * N.K i) else 0)) ∂(Measure.pi fun _ : Fin N' => N.μ)
        ≤ ∫⁻ z, (Km (padHist N' z) + Bm (padHist N' z)) ∂(Measure.pi fun _ : Fin N' => N.μ) :=
          lintegral_mono fun z => hpath _
      _ = ∫⁻ z, Km (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ)
          + ∫⁻ z, Bm (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ) :=
          lintegral_add_left (f := fun z => Km (padHist N' z)) (hKmm.comp hD) _
      _ ≤ ∫⁻ z, Km (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ)
          + (∫⁻ z, Fm (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ) + CH) :=
          add_le_add le_rfl (hcHp T)
      _ ≤ ∫⁻ z, (Km (padHist N' z) + Fm (padHist N' z)) ∂(Measure.pi fun _ : Fin N' => N.μ) + CH := by
          rw [← add_assoc]; exact add_le_add (le_lintegral_add _ _) le_rfl
      _ ≤ ∫⁻ _z, T * ENNReal.ofReal (N.F i (c.S i) + N.K i) ∂(Measure.pi fun _ : Fin N' => N.μ) + CH :=
          add_le_add (lintegral_mono fun z => hKF _) le_rfl
      _ = T * ENNReal.ofReal (N.F i (c.S i) + N.K i) + CH := by
          rw [lintegral_const, measure_univ, mul_one]

end ret

section init

variable {n : ℕ} (N : Network n) (x : InitState n)

lemma minit_bd (hN : N.Standing) : ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ N' : ℕ,
    ∫⁻ z, ENNReal.ofReal (minit N x (padHist N' z)) ∂(Measure.pi fun _ : Fin N' => N.μ) ≤ C := by
  set a : Fin n → ℝ := fun i => |x.I i| + ∑ s ∈ Finset.range N.Tpipe, |x.retPipe i s| with ha
  set cm : ℝ := ∑ i, (N.L i : ℝ) * ((N.H i + N.p) * (a i + 1)) with hcm
  set m : ℝ≥0∞ := ∑ i, ∫⁻ a, (a i : ℝ≥0∞) ∂N.μ with hm
  have hmf : m ≠ ∞ := ENNReal.sum_ne_top.2 fun i _ => (hN.mean_lt_top i).ne
  refine ⟨ENNReal.ofReal cm * (1 + N.Tpipe * m), ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hmf⟩),
    fun N' => ?_⟩
  have hcm0 : 0 ≤ cm := Finset.sum_nonneg fun i _ => by
    have : 0 ≤ N.H i + N.p := by linarith [hN.H_pos i, hN.p_pos]
    have : 0 ≤ a i := add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun s _ => abs_nonneg _)
    positivity
  have hpath : ∀ d : ℕ → DemandVec n, minit N x d ≤ cm * (1 + Dall d N.Tpipe) := by
    intro d
    have hD := Dall_nonneg d N.Tpipe
    unfold minit
    rw [hcm, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have hHp : 0 ≤ N.H i + N.p := by linarith [hN.H_pos i, hN.p_pos]
    have ha0 : 0 ≤ a i := add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun s _ => abs_nonneg _)
    calc ∑ t ∈ Finset.range (N.L i), cH N i (x.I i + ∑ s ∈ Finset.range (t + 1),
          (x.retPipe i s - ((d s i : ℝ≥0) : ℝ)))
        ≤ ∑ _t ∈ Finset.range (N.L i), (N.H i + N.p) * (a i + 1) * (1 + Dall d N.Tpipe) :=
          Finset.sum_le_sum fun t ht => by
            have ht' : t + 1 ≤ N.Tpipe := by have := L_le_Tpipe N i; simp at ht; omega
            refine (cH_le_abs N hN i _).trans ?_
            have habs : |x.I i + ∑ s ∈ Finset.range (t + 1), (x.retPipe i s - ((d s i : ℝ≥0) : ℝ))|
                ≤ a i + Dall d N.Tpipe := by
              calc |x.I i + ∑ s ∈ Finset.range (t + 1), (x.retPipe i s - ((d s i : ℝ≥0) : ℝ))|
                  ≤ |x.I i| + |∑ s ∈ Finset.range (t + 1), (x.retPipe i s - ((d s i : ℝ≥0) : ℝ))| :=
                    abs_add_le _ _
                _ ≤ |x.I i| + ∑ s ∈ Finset.range (t + 1), |x.retPipe i s - ((d s i : ℝ≥0) : ℝ)| := by
                    gcongr; exact Finset.abs_sum_le_sum_abs _ _
                _ ≤ |x.I i| + ∑ s ∈ Finset.range (t + 1), (|x.retPipe i s| + ((d s i : ℝ≥0) : ℝ)) := by
                    gcongr with s
                    calc |x.retPipe i s - ((d s i : ℝ≥0) : ℝ)|
                        ≤ |x.retPipe i s| + |((d s i : ℝ≥0) : ℝ)| := abs_sub _ _
                      _ = |x.retPipe i s| + ((d s i : ℝ≥0) : ℝ) := by
                          rw [abs_of_nonneg (NNReal.coe_nonneg _)]
                _ = |x.I i| + ∑ s ∈ Finset.range (t + 1), |x.retPipe i s|
                    + ∑ s ∈ Finset.range (t + 1), ((d s i : ℝ≥0) : ℝ) := by
                    rw [Finset.sum_add_distrib, add_assoc]
                _ ≤ a i + Dall d N.Tpipe := by
                    have h1 : ∑ s ∈ Finset.range (t + 1), |x.retPipe i s|
                        ≤ ∑ s ∈ Finset.range N.Tpipe, |x.retPipe i s| :=
                      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 ht')
                        fun _ _ _ => abs_nonneg _
                    have h2 := (dsum_le_Dall d (t + 1) i).trans (Dall_mono d ht')
                    simp only [ha]; linarith
            calc (N.H i + N.p) * |x.I i + ∑ s ∈ Finset.range (t + 1),
                  (x.retPipe i s - ((d s i : ℝ≥0) : ℝ))|
                ≤ (N.H i + N.p) * (a i + Dall d N.Tpipe) := mul_le_mul_of_nonneg_left habs hHp
              _ ≤ (N.H i + N.p) * (a i + 1) * (1 + Dall d N.Tpipe) := by
                  rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by nlinarith) hHp
      _ = (N.L i : ℝ) * ((N.H i + N.p) * (a i + 1)) * (1 + Dall d N.Tpipe) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  calc ∫⁻ z, ENNReal.ofReal (minit N x (padHist N' z)) ∂(Measure.pi fun _ : Fin N' => N.μ)
      ≤ ∫⁻ z, ENNReal.ofReal cm * ENNReal.ofReal (1 + Dall (padHist N' z) N.Tpipe)
          ∂(Measure.pi fun _ : Fin N' => N.μ) := lintegral_mono fun z => by
        rw [← ENNReal.ofReal_mul hcm0]; exact ENNReal.ofReal_le_ofReal (hpath _)
    _ = ENNReal.ofReal cm * ∫⁻ z, ENNReal.ofReal (1 + Dall (padHist N' z) N.Tpipe)
          ∂(Measure.pi fun _ : Fin N' => N.μ) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal cm * (1 + N.Tpipe * m) := by gcongr; exact lin_exp N N' N.Tpipe

end init

end OWMR.Asm

end Part13

section Part14

/-! Assembly, part 14: the expected cost over a horizon, split into its components. -/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open OWMR OWMR.S6


namespace OWMR.Asm

section fin

variable {n : ℕ} (N : Network n) (x : InitState n) (c : ConChoice n)

lemma TI_meas (t : ℕ) : MeasurableSet {d : ℕ → DemandVec n | TI N x c d t} := by
  unfold TI
  by_cases hL : N.L0 + 1 ≤ t
  · simp only [hL, true_and]; exact (act_meas N x c _).compl
  · simp only [hL, false_and, not_false_eq_true, Set.setOf_true]; exact MeasurableSet.univ

lemma minit_meas : Measurable fun d : ℕ → DemandVec n => minit N x d := by
  have hcH : ∀ i, Measurable fun y => cH N i y := fun i => by unfold cH; fun_prop
  unfold minit
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun t _ => (hcH i).comp
    (measurable_const.add (Finset.measurable_sum _ fun s _ => measurable_const.sub (meas_coord s i)))

lemma supT_meas (t : ℕ) : Measurable fun d : ℕ → DemandVec n => supT N x c d t := by
  have h1 : MeasurableSet {d : ℕ → DemandVec n | N.L0 ≤ t ∧ act N x c d (t - N.L0)} := by
    by_cases hL : N.L0 ≤ t
    · simp only [hL, true_and]; exact act_meas N x c (t - N.L0)
    · simp only [hL, false_and, Set.setOf_false]; exact MeasurableSet.empty
  unfold supT
  refine (Measurable.ite (act_meas N x c t) (measurable_const.mul (Measurable.ite
    (measurableSet_lt measurable_const (q0_meas N x c t)) measurable_const measurable_const))
    measurable_const).add (Measurable.ite h1 ((meas_whLoss N.h N.p).comp
      ((Ypost_meas N x c _).sub (meas_window (t - N.L0) N.L0))) measurable_const)

lemma retT_meas (t : ℕ) (i : Fin n) : Measurable fun d : ℕ → DemandVec n => retT N x c d t i := by
  have hcH : Measurable fun y => cH N i y := by unfold cH; fun_prop
  have h2 : MeasurableSet {d : ℕ → DemandVec n | act N x c d t ∧ ¬ c.batch i = true} :=
    (act_meas N x c t).inter (MeasurableSet.const _)
  unfold retT
  exact ((Measurable.ite (act_meas N x c t) (measurable_const.mul
    (measurable_const.sub (Ph_meas N x c t i))) measurable_const).add
    (Measurable.ite h2 measurable_const measurable_const)).add
    (hcH.comp ((Pos'_meas N x c t i).sub (Dblk_meas N t i)))

lemma Zexp_thE_meas (s : ℕ) (i : Fin n) :
    Measurable fun d : ℕ → DemandVec n => Zexp N x c d s i (thE N x c s i d) := by
  have hth := thE_meas N x c s i
  have hship : ∀ k, Measurable fun d : ℕ → DemandVec n => shippedPath (q N x c d s i)
      (thE N x c s i d) (fun k => A N x c d s i (s + k)) k :=
    ship_meas (fun d => q N x c d s i) (fun d => thE N x c s i d)
      (fun k d => A N x c d s i (s + k)) (q_meas N x c s i) hth (fun k => A_meas N x c s i (s + k))
  unfold Zexp Ncnt
  exact (measurable_const.mul (measurable_const.add (Measurable.ite
    (measurableSet_lt hth measurable_const) measurable_const measurable_const))).add
    (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
      (((A_meas N x c s i (s + k)).sub (hship k)).sub (X_meas N x c (s + k))).max measurable_const))

lemma supT_nonneg (hN : N.Standing) (d : ℕ → DemandVec n) (t : ℕ) : 0 ≤ supT N x c d t := by
  unfold supT
  refine add_nonneg ?_ ?_
  · split_ifs
    · exact mul_nonneg hN.K0_nonneg (by norm_num)
    · simp
    · exact le_rfl
  · split_ifs
    · exact whLoss_nonneg _ _ _ hN.h_pos.le hN.p_pos.le
    · exact le_rfl

lemma retT_nonneg (hN : N.Standing) (hsS : ∀ i, c.s i ≤ c.S i) (d : ℕ → DemandVec n) (t : ℕ)
    (i : Fin n) : 0 ≤ retT N x c d t i := by
  unfold retT
  have h1 : 0 ≤ (if act N x c d t then N.h * (c.S i - Ph N x c d t i) else 0) := by
    split_ifs
    · exact mul_nonneg hN.h_pos.le (sub_nonneg.2 (Ph_bounds N x c hsS d t i).2)
    · exact le_rfl
  have h2 : 0 ≤ (if act N x c d t ∧ ¬ c.batch i = true then N.K i else 0) := by
    split_ifs
    · exact hN.K_nonneg i
    · exact le_rfl
  exact add_nonneg (add_nonneg h1 h2) (cH_nonneg N hN i _)

lemma mrun_split (d : ℕ → DemandVec n) (t : ℕ) :
    mrun N x c d t = supT N x c d t + ∑ i, retT N x c d t i := by
  unfold mrun supT retT
  simp only [Finset.sum_add_distrib]
  by_cases ha : act N x c d t
  · simp only [ha, true_and, if_true]
    rw [Finset.sum_filter]; ring
  · simp only [ha, false_and, if_false, Finset.sum_const_zero]; ring

section pol

variable (θ : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)
  (hdisp : ∀ d t i, (conPolicy N x c).dispatch t d i = if act N x c d t then
        ∑ s ∈ Finset.range (t + 1),
          ((if c.batch i then shippedPath (q N x c d s i) (θ d s i)
                (fun k => A N x c d s i (s + k)) (t - s)
              else A N x c d s i t)
            - if s < t then (if c.batch i then
                shippedPath (q N x c d s i) (θ d s i) (fun k => A N x c d s i (s + k)) (t - 1 - s)
              else A N x c d s i (t - 1)) else 0)
        else if t = N.Tpipe - 1 ∧ i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
        else 0)
  (hord : ∀ d t, (conPolicy N x c).order t d = q0 N x c d t)

include hdisp hord in
lemma pc_nonneg (hN : N.Standing) (hx : x.Valid) (hsS : ∀ i, c.s i ≤ c.S i) (hs0S : c.s0 ≤ c.S0)
    (d : ℕ → DemandVec n) (t : ℕ) :
    0 ≤ Policy.periodCost N x (conPolicy N x c).toPolicy () d t := by
  have hW : 0 ≤ Policy.whStock N x (conPolicy N x c).toPolicy () d t := by
    by_cases ha : act N x c d t
    · rw [whStock_run N x c θ hdisp hord d t ha]
      have h1 : ∑ r ∈ Finset.range (t + 1), ∑ i, sh N x c θ d r i t
          ≤ ∑ r ∈ Finset.range (t + 1), ∑ i, A N x c d r i t :=
        Finset.sum_le_sum fun r hr => Finset.sum_le_sum fun i _ =>
          (sh_props N x c θ hsS hs0S d r i t (by simp at hr; omega)).2.1
      rw [sum_A N x c hsS d t] at h1
      have h2 : max 0 (min (V N x c d t) (Cq N x c d t)) ≤ V N x c d t :=
        max_le (V_nonneg N x c hs0S d t) (min_le_left _ _)
      linarith
    · exact (whStock_prep N x c θ hdisp hord hx hs0S d t ha).1
  unfold Policy.periodCost
  refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) (mul_nonneg hN.h_pos.le hW)) ?_
  · exact mul_nonneg hN.K0_nonneg (by split_ifs <;> norm_num)
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hN.K_nonneg i) (by split_ifs <;> norm_num)
  · exact Finset.sum_nonneg fun i _ => add_nonneg (mul_nonneg (hN.H_pos i).le (le_max_right _ _))
      (mul_nonneg hN.p_pos.le (le_max_right _ _))

end pol

end fin

section chain

variable {n : ℕ} (N : Network n) (x : InitState n) (c : ConChoice n)

lemma ctr_nonneg (hN : N.Standing) (hx : x.Valid) : 0 ≤ ctr N x c := by
  have hh := hN.h_pos.le; have hp := hN.p_pos.le; have hK := hN.K_nonneg
  have hW0 : 0 ≤ W0 N x := by
    unfold W0; obtain ⟨h1, h2, -⟩ := hx
    exact add_nonneg h1 (Finset.sum_nonneg fun s _ => h2 s)
  unfold ctr
  have h1 : 0 ≤ ∑ i, N.K i + N.h * W0 N x :=
    add_nonneg (Finset.sum_nonneg fun i _ => hK i) (mul_nonneg hh hW0)
  have h2 : 0 ≤ (N.h + N.p) * (|∑ i, (IP N x c (fun _ => 0) 0 i - c.S i)| + 1) :=
    mul_nonneg (by linarith) (by positivity)
  have h3 : 0 ≤ ∑ i, (3 * N.K i + (N.h + N.p) * ((N.L0 + 1 : ℝ)
      * (|c.S i - IP N x c (fun _ => 0) 0 i| + 1))) :=
    Finset.sum_nonneg fun i _ => add_nonneg (by linarith [hK i])
      (mul_nonneg (by linarith) (by positivity))
  linarith

variable (θ : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)
  (hθd : ∀ d d' s, (∀ r < s, d r = d' r) → ∀ i, θ d s i = θ d' s i)
  (hdisp : ∀ d t i, (conPolicy N x c).dispatch t d i = if act N x c d t then
        ∑ s ∈ Finset.range (t + 1),
          ((if c.batch i then shippedPath (q N x c d s i) (θ d s i)
                (fun k => A N x c d s i (s + k)) (t - s)
              else A N x c d s i t)
            - if s < t then (if c.batch i then
                shippedPath (q N x c d s i) (θ d s i) (fun k => A N x c d s i (s + k)) (t - 1 - s)
              else A N x c d s i (t - 1)) else 0)
        else if t = N.Tpipe - 1 ∧ i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
        else 0)
  (hord : ∀ d t, (conPolicy N x c).order t d = q0 N x c d t)
  (hident : ∀ d s i, 0 < s → act N x c d (s - 1) → 0 < q N x c d s i → c.batch i = true →
        ∃ σ : EngState n,
          θ d s i = conRule N c σ s (∑ r ∈ Finset.range s,
              (if 0 < r ∧ act N x c d (r - 1) then
                ((List.finRange n).filter (fun j => decide (0 < q N x c d r j))).length else 0)
            + ((List.finRange n).filter (fun j => decide (0 < q N x c d s j))).idxOf i + 1) i
              (q N x c d s i) ∧
          ∀ (ds : Fin N.L0 → DemandVec n) (k : ℕ), k ≤ N.L0 →
            idealAlloc N c.params σ s i (q N x c d s i) (padHist N.L0 ds) k = A N x c d s i (s + k) ∧
            idealDepletion N c.params σ s (padHist N.L0 ds) k
              = ∑ j, (c.S j - Ph N x c (fun r => if r < s then d r else padHist N.L0 ds (r - s))
                  (s + k) j))

/-- The pathwise split of the explicit bound after derandomization. -/
lemma split_path (hN : N.Standing) (hx : x.Valid) (hsS : ∀ i, c.s i ≤ c.S i) (hs0 : 0 ≤ c.s0)
    (hs0S : c.s0 ≤ c.S0) (hw : ∀ i, c.batch i = true → c.s i < c.S i) (d : ℕ → DemandVec n) (T : ℕ) :
    ENNReal.ofReal (minit N x d + ∑ t ∈ Finset.range T, (mrun N x c d t
        + 3 * ctr N x c * (if TI N x c d t then 1 + Dall d t else 0)))
      + ∑ s ∈ Finset.range T, ∑ i, (if ord N x c d s i then ENNReal.ofReal (Bx N x c d s i) else 0)
    ≤ ENNReal.ofReal (minit N x d)
      + ENNReal.ofReal (3 * ctr N x c) * ∑ t ∈ Finset.range T,
          (if TI N x c d t then ENNReal.ofReal (1 + Dall d t) else 0)
      + ∑ t ∈ Finset.range T, ENNReal.ofReal (supT N x c d t)
      + ∑ i, (∑ t ∈ Finset.range T, ENNReal.ofReal (retT N x c d t i)
          + ∑ t ∈ Finset.range T, (if ord N x c d t i then ENNReal.ofReal (7 / 3 * N.K i) else 0))
      + ENNReal.ofReal (∑ t ∈ Finset.range (T + N.L0), pp N x c d t) := by
  have hh := hN.h_pos.le; have hp := hN.p_pos.le
  have hc0 := ctr_nonneg N x c hN hx
  -- the real bound, split
  have e1 : minit N x d + ∑ t ∈ Finset.range T, (mrun N x c d t
        + 3 * ctr N x c * (if TI N x c d t then 1 + Dall d t else 0))
      = minit N x d + (∑ t ∈ Finset.range T, supT N x c d t
        + ∑ i, ∑ t ∈ Finset.range T, retT N x c d t i)
        + 3 * ctr N x c * ∑ t ∈ Finset.range T, (if TI N x c d t then 1 + Dall d t else 0) := by
    simp only [mrun_split, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.range T) (t := Finset.univ)]
    ring
  have hTI0 : 0 ≤ ∑ t ∈ Finset.range T, (if TI N x c d t then 1 + Dall d t else 0) :=
    Finset.sum_nonneg fun t _ => by split_ifs <;> linarith [Dall_nonneg d t]
  have hR : ENNReal.ofReal (minit N x d + ∑ t ∈ Finset.range T, (mrun N x c d t
        + 3 * ctr N x c * (if TI N x c d t then 1 + Dall d t else 0)))
      ≤ ENNReal.ofReal (minit N x d)
        + ENNReal.ofReal (3 * ctr N x c) * ∑ t ∈ Finset.range T,
            (if TI N x c d t then ENNReal.ofReal (1 + Dall d t) else 0)
        + ∑ t ∈ Finset.range T, ENNReal.ofReal (supT N x c d t)
        + ∑ i, ∑ t ∈ Finset.range T, ENNReal.ofReal (retT N x c d t i) := by
    rw [e1]
    have hs1 : ENNReal.ofReal (∑ t ∈ Finset.range T, supT N x c d t)
        = ∑ t ∈ Finset.range T, ENNReal.ofReal (supT N x c d t) :=
      ENNReal.ofReal_sum_of_nonneg fun t _ => supT_nonneg N x c hN d t
    have hs2 : ENNReal.ofReal (∑ i, ∑ t ∈ Finset.range T, retT N x c d t i)
        = ∑ i, ∑ t ∈ Finset.range T, ENNReal.ofReal (retT N x c d t i) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun t _ =>
        retT_nonneg N x c hN hsS d t i]
      exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_sum_of_nonneg fun t _ =>
        retT_nonneg N x c hN hsS d t i
    have hs3 : ENNReal.ofReal (3 * ctr N x c * ∑ t ∈ Finset.range T,
          (if TI N x c d t then 1 + Dall d t else 0))
        = ENNReal.ofReal (3 * ctr N x c) * ∑ t ∈ Finset.range T,
            (if TI N x c d t then ENNReal.ofReal (1 + Dall d t) else 0) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg fun t _ => by
        split_ifs <;> linarith [Dall_nonneg d t]]
      congr 1
      exact Finset.sum_congr rfl fun t _ => by split_ifs <;> simp
    calc ENNReal.ofReal (minit N x d + (∑ t ∈ Finset.range T, supT N x c d t
          + ∑ i, ∑ t ∈ Finset.range T, retT N x c d t i)
          + 3 * ctr N x c * ∑ t ∈ Finset.range T, (if TI N x c d t then 1 + Dall d t else 0))
        ≤ ENNReal.ofReal (minit N x d) + (ENNReal.ofReal (∑ t ∈ Finset.range T, supT N x c d t)
          + ENNReal.ofReal (∑ i, ∑ t ∈ Finset.range T, retT N x c d t i))
          + ENNReal.ofReal (3 * ctr N x c * ∑ t ∈ Finset.range T,
            (if TI N x c d t then 1 + Dall d t else 0)) := by
          refine ENNReal.ofReal_add_le.trans (add_le_add (ENNReal.ofReal_add_le.trans
            (add_le_add le_rfl ENNReal.ofReal_add_le)) le_rfl)
      _ = _ := by rw [hs1, hs2, hs3]; ring
  -- the credited bounds
  have hB : ∀ s i, (if ord N x c d s i then ENNReal.ofReal (Bx N x c d s i) else 0)
      ≤ (if ord N x c d s i then ENNReal.ofReal (7 / 3 * N.K i) else 0)
        + ENNReal.ofReal (if ord N x c d s i then ∑ k ∈ Finset.range (N.L0 + 1),
          (if 0 < A N x c d s i (s + k) ∧ A N x c d s i (s + k) < q N x c d s i then
            (N.h + N.p) * crA N x c d s i (s + k) else 0) else 0) := by
    intro s i
    by_cases ho : ord N x c d s i
    · rw [if_pos ho, if_pos ho, if_pos ho]
      unfold Bx
      refine ENNReal.ofReal_add_le.trans (le_of_eq ?_)
      congr 2
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp
    · rw [if_neg ho, if_neg ho, if_neg ho, ENNReal.ofReal_zero, add_zero]
  have hcr0 : ∀ s i, 0 ≤ (if ord N x c d s i then ∑ k ∈ Finset.range (N.L0 + 1),
      (if 0 < A N x c d s i (s + k) ∧ A N x c d s i (s + k) < q N x c d s i then
        (N.h + N.p) * crA N x c d s i (s + k) else 0) else 0) := by
    intro s i
    split_ifs
    · refine Finset.sum_nonneg fun k _ => ?_
      split_ifs with hpa
      · unfold crA
        have : 0 < q N x c d s i := lt_trans hpa.1 hpa.2
        positivity
      · exact le_rfl
    · exact le_rfl
  have hBsum : ∑ s ∈ Finset.range T, ∑ i, (if ord N x c d s i then ENNReal.ofReal (Bx N x c d s i) else 0)
      ≤ ∑ i, ∑ t ∈ Finset.range T, (if ord N x c d t i then ENNReal.ofReal (7 / 3 * N.K i) else 0)
        + ENNReal.ofReal (∑ t ∈ Finset.range (T + N.L0), pp N x c d t) := by
    calc ∑ s ∈ Finset.range T, ∑ i, (if ord N x c d s i then ENNReal.ofReal (Bx N x c d s i) else 0)
        ≤ ∑ s ∈ Finset.range T, ∑ i, ((if ord N x c d s i then ENNReal.ofReal (7 / 3 * N.K i) else 0)
          + ENNReal.ofReal (if ord N x c d s i then ∑ k ∈ Finset.range (N.L0 + 1),
            (if 0 < A N x c d s i (s + k) ∧ A N x c d s i (s + k) < q N x c d s i then
              (N.h + N.p) * crA N x c d s i (s + k) else 0) else 0)) :=
          Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun i _ => hB s i
      _ = ∑ i, ∑ t ∈ Finset.range T, (if ord N x c d t i then ENNReal.ofReal (7 / 3 * N.K i) else 0)
          + ENNReal.ofReal (∑ s ∈ Finset.range T, ∑ i, (if ord N x c d s i then
            ∑ k ∈ Finset.range (N.L0 + 1),
            (if 0 < A N x c d s i (s + k) ∧ A N x c d s i (s + k) < q N x c d s i then
              (N.h + N.p) * crA N x c d s i (s + k) else 0) else 0)) := by
          simp only [Finset.sum_add_distrib]
          rw [Finset.sum_comm (s := Finset.range T) (t := Finset.univ)]
          congr 1
          rw [ENNReal.ofReal_sum_of_nonneg fun s _ => Finset.sum_nonneg fun i _ => hcr0 s i]
          exact Finset.sum_congr rfl fun s _ =>
            (ENNReal.ofReal_sum_of_nonneg fun i _ => hcr0 s i).symm
      _ ≤ _ := add_le_add le_rfl (ENNReal.ofReal_le_ofReal
          (sum_cr_le N x c hN hsS hs0 hs0S hw d T))
  calc ENNReal.ofReal (minit N x d + ∑ t ∈ Finset.range T, (mrun N x c d t
        + 3 * ctr N x c * (if TI N x c d t then 1 + Dall d t else 0)))
      + ∑ s ∈ Finset.range T, ∑ i, (if ord N x c d s i then ENNReal.ofReal (Bx N x c d s i) else 0)
      ≤ (ENNReal.ofReal (minit N x d)
        + ENNReal.ofReal (3 * ctr N x c) * ∑ t ∈ Finset.range T,
            (if TI N x c d t then ENNReal.ofReal (1 + Dall d t) else 0)
        + ∑ t ∈ Finset.range T, ENNReal.ofReal (supT N x c d t)
        + ∑ i, ∑ t ∈ Finset.range T, ENNReal.ofReal (retT N x c d t i))
        + (∑ i, ∑ t ∈ Finset.range T, (if ord N x c d t i then ENNReal.ofReal (7 / 3 * N.K i) else 0)
        + ENNReal.ofReal (∑ t ∈ Finset.range (T + N.L0), pp N x c d t)) := add_le_add hR hBsum
    _ = _ := by rw [Finset.sum_add_distrib]; ring

end chain

end OWMR.Asm

end Part14

section Part15

/-! Assembly, part 15: the expected cost over a horizon. -/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open OWMR OWMR.S6


namespace OWMR.Asm

section final

variable {n : ℕ} (N : Network n) (x : InitState n) (c : ConChoice n)
  (θ : (ℕ → DemandVec n) → ℕ → Fin n → ℝ)
  (hθd : ∀ d d' s, (∀ r < s, d r = d' r) → ∀ i, θ d s i = θ d' s i)
  (hdisp : ∀ d t i, (conPolicy N x c).dispatch t d i = if act N x c d t then
        ∑ s ∈ Finset.range (t + 1),
          ((if c.batch i then shippedPath (q N x c d s i) (θ d s i)
                (fun k => A N x c d s i (s + k)) (t - s)
              else A N x c d s i t)
            - if s < t then (if c.batch i then
                shippedPath (q N x c d s i) (θ d s i) (fun k => A N x c d s i (s + k)) (t - 1 - s)
              else A N x c d s i (t - 1)) else 0)
        else if t = N.Tpipe - 1 ∧ i = c.sendTo then x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
        else 0)
  (hord : ∀ d t, (conPolicy N x c).order t d = q0 N x c d t)
  (hident : ∀ d s i, 0 < s → act N x c d (s - 1) → 0 < q N x c d s i → c.batch i = true →
        ∃ σ : EngState n,
          θ d s i = conRule N c σ s (∑ r ∈ Finset.range s,
              (if 0 < r ∧ act N x c d (r - 1) then
                ((List.finRange n).filter (fun j => decide (0 < q N x c d r j))).length else 0)
            + ((List.finRange n).filter (fun j => decide (0 < q N x c d s j))).idxOf i + 1) i
              (q N x c d s i) ∧
          ∀ (ds : Fin N.L0 → DemandVec n) (k : ℕ), k ≤ N.L0 →
            idealAlloc N c.params σ s i (q N x c d s i) (padHist N.L0 ds) k = A N x c d s i (s + k) ∧
            idealDepletion N c.params σ s (padHist N.L0 ds) k
              = ∑ j, (c.S j - Ph N x c (fun r => if r < s then d r else padHist N.L0 ds (r - s))
                  (s + k) j))

include hθd hdisp hord hident in
lemma exp_chain (hN : N.Standing) (hx : x.Valid) (hsS : ∀ i, c.s i ≤ c.S i) (hs0 : 0 ≤ c.s0)
    (hs0S : c.s0 ≤ c.S0) (hw : ∀ i, c.batch i = true → c.s i < c.S i)
    (hθ : ∀ d s i, 0 < θ d s i ∧ θ d s i < 1) (T : ℕ) :
    expCost N x (conPolicy N x c).toPolicy (Measure.dirac ()) T
      ≤ ∫⁻ z, ENNReal.ofReal (minit N x (padHist (T + Mh N) z))
            ∂(Measure.pi fun _ : Fin (T + Mh N) => N.μ)
        + ENNReal.ofReal (3 * ctr N x c) * ∫⁻ z, ∑ t ∈ Finset.range T,
            (if TI N x c (padHist (T + Mh N) z) t then
              ENNReal.ofReal (1 + Dall (padHist (T + Mh N) z) t) else 0)
            ∂(Measure.pi fun _ : Fin (T + Mh N) => N.μ)
        + ∫⁻ z, ∑ t ∈ Finset.range T, ENNReal.ofReal (supT N x c (padHist (T + Mh N) z) t)
            ∂(Measure.pi fun _ : Fin (T + Mh N) => N.μ)
        + ∑ i, ∫⁻ z, (∑ t ∈ Finset.range T, ENNReal.ofReal (retT N x c (padHist (T + Mh N) z) t i)
            + ∑ t ∈ Finset.range T, (if ord N x c (padHist (T + Mh N) z) t i then
                ENNReal.ofReal (7 / 3 * N.K i) else 0)) ∂(Measure.pi fun _ : Fin (T + Mh N) => N.μ)
        + ∫⁻ z, ENNReal.ofReal (∑ t ∈ Finset.range (T + N.L0), pp N x c (padHist (T + Mh N) z) t)
            ∂(Measure.pi fun _ : Fin (T + Mh N) => N.μ)
        + 1 := by
  set N' := T + Mh N with hN'
  have hD := measurable_padHist' (α := DemandVec n) N'
  set R1 : (ℕ → DemandVec n) → ℝ := fun d => minit N x d + ∑ t ∈ Finset.range T, (mrun N x c d t
    + 3 * ctr N x c * (if TI N x c d t then 1 + Dall d t else 0)) with hR1
  set g : ℕ → Fin n → (ℕ → DemandVec n) → ℝ≥0∞ := fun s i d => if ord N x c d s i then
    ENNReal.ofReal (Zexp N x c d s i (thE N x c s i d)) else 0 with hg
  set bx : ℕ → Fin n → (ℕ → DemandVec n) → ℝ≥0∞ := fun s i d => if ord N x c d s i then
    ENNReal.ofReal (Bx N x c d s i) else 0 with hbx
  set tl : ℕ → Fin n → (ℕ → DemandVec n) → ℝ≥0∞ := fun s i d => if ord N x c d s i then
    (2 : ℝ≥0∞)⁻¹ ^ jE N x c s i d else 0 with htl
  have hgm : ∀ s i, Measurable (g s i) := fun s i =>
    Measurable.ite (ord_meas N x c s i) (Zexp_thE_meas N x c s i).ennreal_ofReal measurable_const
  -- the pathwise bound
  have s2 : ∀ d : ℕ → DemandVec n, ∑ t ∈ Finset.range T,
      ENNReal.ofReal (Policy.periodCost N x (conPolicy N x c).toPolicy () d t)
      ≤ ENNReal.ofReal (R1 d) + ∑ s ∈ Finset.range T, ∑ i, g s i d := by
    intro d
    have hZ : ∀ s i, 0 ≤ (if ord N x c d s i then Zexp N x c d s i (thE N x c s i d) else 0) :=
      fun s i => by split_ifs; exacts [Zexp_nonneg N x c hN d s i _, le_rfl]
    rw [← ENNReal.ofReal_sum_of_nonneg fun t _ => pc_nonneg N x c θ hdisp hord hN hx hsS hs0S d t]
    refine (ENNReal.ofReal_le_ofReal
      (cost_explicit N x c θ hdisp hord hident hN hx hsS hs0 hs0S hθ d T)).trans ?_
    refine ENNReal.ofReal_add_le.trans (add_le_add le_rfl (le_of_eq ?_))
    rw [ENNReal.ofReal_sum_of_nonneg fun s _ => Finset.sum_nonneg fun i _ => hZ s i]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ => hZ s i]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hg]
    split_ifs <;> simp
  -- measurability of the components
  have hmA : Measurable fun z : Fin N' → DemandVec n => ENNReal.ofReal (minit N x (padHist N' z)) :=
    ((minit_meas N x).ennreal_ofReal).comp hD
  have hmB : Measurable fun z : Fin N' → DemandVec n => ENNReal.ofReal (3 * ctr N x c)
      * ∑ t ∈ Finset.range T, (if TI N x c (padHist N' z) t then
          ENNReal.ofReal (1 + Dall (padHist N' z) t) else 0) :=
    measurable_const.mul ((Finset.measurable_sum _ fun t _ => Measurable.ite (TI_meas N x c t)
      ((measurable_const.add (Dall_meas t)).ennreal_ofReal) measurable_const).comp hD)
  have hmC : Measurable fun z : Fin N' → DemandVec n =>
      ∑ t ∈ Finset.range T, ENNReal.ofReal (supT N x c (padHist N' z) t) :=
    (Finset.measurable_sum _ fun t _ => (supT_meas N x c t).ennreal_ofReal).comp hD
  have hmD : ∀ i, Measurable fun z : Fin N' → DemandVec n =>
      (∑ t ∈ Finset.range T, ENNReal.ofReal (retT N x c (padHist N' z) t i)
        + ∑ t ∈ Finset.range T, (if ord N x c (padHist N' z) t i then
          ENNReal.ofReal (7 / 3 * N.K i) else 0)) := fun i =>
    ((Finset.measurable_sum _ fun t _ => (retT_meas N x c t i).ennreal_ofReal).add
      (Finset.measurable_sum _ fun t _ => Measurable.ite (ord_meas N x c t i) measurable_const
        measurable_const)).comp hD
  have hmG : Measurable fun z : Fin N' → DemandVec n =>
      ∑ s ∈ Finset.range T, ∑ i, g s i (padHist N' z) :=
    Finset.measurable_sum _ fun s _ => Finset.measurable_sum _ fun i _ => (hgm s i).comp hD
  have htol : ∫⁻ z, ∑ s ∈ Finset.range T, ∑ i, tl s i (padHist N' z)
      ∂(Measure.pi fun _ : Fin N' => N.μ) ≤ 1 := by
    calc ∫⁻ z, ∑ s ∈ Finset.range T, ∑ i, tl s i (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ)
        ≤ ∫⁻ _z, (1 : ℝ≥0∞) ∂(Measure.pi fun _ : Fin N' => N.μ) :=
          lintegral_mono fun z => tol_sum N x c hsS _ T
      _ = 1 := by rw [lintegral_const, measure_univ, mul_one]
  calc expCost N x (conPolicy N x c).toPolicy (Measure.dirac ()) T
      ≤ ∫⁻ z, ∑ t ∈ Finset.range T, ENNReal.ofReal
          (Policy.periodCost N x (conPolicy N x c).toPolicy () (padHist N' z) t)
          ∂(Measure.pi fun _ : Fin N' => N.μ) := expCost_le N x c θ hθd hdisp hord T (Mh N)
    _ ≤ ∫⁻ z, (ENNReal.ofReal (R1 (padHist N' z)) + ∑ s ∈ Finset.range T, ∑ i, g s i (padHist N' z))
          ∂(Measure.pi fun _ : Fin N' => N.μ) := lintegral_mono fun z => s2 _
    _ = ∫⁻ z, ENNReal.ofReal (R1 (padHist N' z)) ∂(Measure.pi fun _ : Fin N' => N.μ)
          + ∑ s ∈ Finset.range T, ∑ i, ∫⁻ z, g s i (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ) := by
        rw [lintegral_add_right _ hmG,
          lintegral_finsetSum (f := fun s z => ∑ i, g s i (padHist N' z)) _ fun s _ =>
            Finset.measurable_sum _ fun i _ => (hgm s i).comp hD]
        congr 1
        exact Finset.sum_congr rfl fun s _ => lintegral_finsetSum
          (f := fun i z => g s i (padHist N' z)) _ fun i _ => (hgm s i).comp hD
    _ ≤ ∫⁻ z, ENNReal.ofReal (R1 (padHist N' z)) ∂(Measure.pi fun _ : Fin N' => N.μ)
          + ∑ s ∈ Finset.range T, ∑ i, (∫⁻ z, bx s i (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ)
            + ∫⁻ z, tl s i (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ)) := by
        refine add_le_add le_rfl (Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun i _ => ?_)
        exact derand N x c hN hsS hs0S N' s i (by simp at hs; simp only [hN', Mh]; omega)
    _ ≤ ∫⁻ z, ENNReal.ofReal (R1 (padHist N' z)) ∂(Measure.pi fun _ : Fin N' => N.μ)
          + (∫⁻ z, ∑ s ∈ Finset.range T, ∑ i, bx s i (padHist N' z) ∂(Measure.pi fun _ : Fin N' => N.μ)
            + ∫⁻ z, ∑ s ∈ Finset.range T, ∑ i, tl s i (padHist N' z)
              ∂(Measure.pi fun _ : Fin N' => N.μ)) := by
        refine add_le_add le_rfl ?_
        simp only [Finset.sum_add_distrib]
        exact add_le_add ((Finset.sum_le_sum fun s _ => sum_lintegral_le _ _ _).trans
          (sum_lintegral_le _ _ _)) ((Finset.sum_le_sum fun s _ => sum_lintegral_le _ _ _).trans
          (sum_lintegral_le _ _ _))
    _ ≤ ∫⁻ z, (ENNReal.ofReal (R1 (padHist N' z)) + ∑ s ∈ Finset.range T, ∑ i, bx s i (padHist N' z))
          ∂(Measure.pi fun _ : Fin N' => N.μ) + 1 := by
        rw [← add_assoc]; exact add_le_add (le_lintegral_add _ _) htol
    _ ≤ ∫⁻ z, (ENNReal.ofReal (minit N x (padHist N' z))
          + ENNReal.ofReal (3 * ctr N x c) * ∑ t ∈ Finset.range T,
            (if TI N x c (padHist N' z) t then ENNReal.ofReal (1 + Dall (padHist N' z) t) else 0)
          + ∑ t ∈ Finset.range T, ENNReal.ofReal (supT N x c (padHist N' z) t)
          + ∑ i, (∑ t ∈ Finset.range T, ENNReal.ofReal (retT N x c (padHist N' z) t i)
            + ∑ t ∈ Finset.range T, (if ord N x c (padHist N' z) t i then
              ENNReal.ofReal (7 / 3 * N.K i) else 0))
          + ENNReal.ofReal (∑ t ∈ Finset.range (T + N.L0), pp N x c (padHist N' z) t))
          ∂(Measure.pi fun _ : Fin N' => N.μ) + 1 :=
        add_le_add (lintegral_mono fun z => split_path N x c hN hx hsS hs0 hs0S hw _ T) le_rfl
    _ = _ := by
        have h2 : Measurable fun z : Fin N' → DemandVec n =>
            ENNReal.ofReal (minit N x (padHist N' z))
            + ENNReal.ofReal (3 * ctr N x c) * ∑ t ∈ Finset.range T,
              (if TI N x c (padHist N' z) t then ENNReal.ofReal (1 + Dall (padHist N' z) t) else 0) :=
          hmA.add hmB
        have h3 : Measurable fun z : Fin N' → DemandVec n =>
            ENNReal.ofReal (minit N x (padHist N' z))
            + ENNReal.ofReal (3 * ctr N x c) * ∑ t ∈ Finset.range T,
              (if TI N x c (padHist N' z) t then ENNReal.ofReal (1 + Dall (padHist N' z) t) else 0)
            + ∑ t ∈ Finset.range T, ENNReal.ofReal (supT N x c (padHist N' z) t) := h2.add hmC
        have h4 : Measurable fun z : Fin N' → DemandVec n =>
            ENNReal.ofReal (minit N x (padHist N' z))
            + ENNReal.ofReal (3 * ctr N x c) * ∑ t ∈ Finset.range T,
              (if TI N x c (padHist N' z) t then ENNReal.ofReal (1 + Dall (padHist N' z) t) else 0)
            + ∑ t ∈ Finset.range T, ENNReal.ofReal (supT N x c (padHist N' z) t)
            + ∑ i, (∑ t ∈ Finset.range T, ENNReal.ofReal (retT N x c (padHist N' z) t i)
              + ∑ t ∈ Finset.range T, (if ord N x c (padHist N' z) t i then
                ENNReal.ofReal (7 / 3 * N.K i) else 0)) :=
          h3.add (Finset.measurable_sum _ fun i _ => hmD i)
        rw [lintegral_add_left h4, lintegral_add_left h3, lintegral_add_left h2,
          lintegral_add_left hmA, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum _ fun i _ => hmD i]

end final

end OWMR.Asm

end Part15

section Part16

/-! Assembly, part 16: Proposition (consolidation upper bound). -/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open OWMR OWMR.S6 OWMR.Asm


theorem solution {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing)
    (hA : N.Associated) (m : ℝ) (hm : 1 ≤ m) (hH : ∀ i, m * N.h ≤ N.H i) (hp : N.h ≤ N.p)
    (x : InitState n) (hx : x.Valid) (c : ConChoice n) (hc : IsConChoice N m c) :
    (conPolicy N x c).avgCost N x
      ≤ 2 * N.J0 (conG m * N.K0) + ENNReal.ofReal (conB m) * ∑ i, N.J i (conZeta m * N.K i) := by
  have hh := hN.h_pos; have hpp := hN.p_pos
  have hret := fun i => con_retailer_budget N hN m hm hH hp c hc i
  obtain ⟨a0, ha0, hs0S, hs0, -, hssup, hJ0a, hsh⟩ := arb_supplier_shortage hn N hN m hm hp c hc
  have hθ0 : ∀ i, 0 < c.initOffset i ∧ c.initOffset i < 1 := hc.2.2.2
  have hsS : ∀ i, c.s i ≤ c.S i := fun i => by
    cases hb : c.batch i
    · exact ((hret i).1 hb).1.le
    · exact ((hret i).2 hb).1.le
  have hw : ∀ i, c.batch i = true → c.s i < c.S i := fun i hb => ((hret i).2 hb).1
  have himm : ∀ i, ¬ c.batch i = true → c.s i = c.S i := fun i hb =>
    ((hret i).1 (by simpa using hb)).1
  obtain ⟨θ, hθ, hθd, hord, hdisp, hident⟩ := engine N x c hsS hs0S hθ0
  -- the trigger level
  have hg : Measurable fun a : DemandVec n => ∑ i ∈ bset c, a i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  set ρ := N.μ.map (fun a : DemandVec n => ∑ i ∈ bset c, a i) with hρ
  have : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map hg.aemeasurable
  have hρm : ∫⁻ x, (x : ℝ≥0∞) ∂ρ < ∞ := by
    rw [hρ, lintegral_map measurable_coe_nnreal_ennreal hg]
    simp only [ENNReal.coe_finset_sum]
    rw [lintegral_finsetSum _ fun i _ => (measurable_pi_apply i).coe_nnreal_ennreal]
    exact ENNReal.sum_lt_top.2 fun i _ => hN.mean_lt_top i
  obtain ⟨y, hy0, hy⟩ := arb_indep_max ρ hρm N.L0 N.h N.p hh hpp
  -- the long-run components
  obtain ⟨Ci, hCif, hCi⟩ := minit_bd N x hN
  obtain ⟨Ct, hCtf, hCt⟩ := TI_bd N x c hN
  have L1 : LR (fun T => ∫⁻ z, ENNReal.ofReal (minit N x (padHist (T + Mh N) z))
      ∂(Measure.pi fun _ : Fin (T + Mh N) => N.μ)) 0 :=
    LR.zero_rate Ci hCif fun T => hCi (T + Mh N)
  have L2 : LR (fun T => ∫⁻ z, ∑ t ∈ Finset.range T, (if TI N x c (padHist (T + Mh N) z) t then
      ENNReal.ofReal (1 + Dall (padHist (T + Mh N) z) t) else 0)
      ∂(Measure.pi fun _ : Fin (T + Mh N) => N.μ)) 0 :=
    LR.zero_rate Ct hCtf fun T => hCt T (T + Mh N) (by unfold Mh; omega)
  have L3 := sup_long N x c hn hN hs0S
  have L4 := LR.sum Finset.univ (fun i T => ∫⁻ z, (∑ t ∈ Finset.range T,
      ENNReal.ofReal (retT N x c (padHist (T + Mh N) z) t i)
      + ∑ t ∈ Finset.range T, (if ord N x c (padHist (T + Mh N) z) t i then
          ENNReal.ofReal (7 / 3 * N.K i) else 0)) ∂(Measure.pi fun _ : Fin (T + Mh N) => N.μ))
    (fun i => if c.batch i = true then ssAvgCost (N.marginal i) (N.F i) (7 / 3 * N.K i) (c.s i) (c.S i)
          + ssAvgCost (N.marginal i) (fun y => N.h * max (c.S i - y) 0) 0 (c.s i) (c.S i)
        else ENNReal.ofReal (N.F i (c.S i) + N.K i))
    (fun i _ => ret_long N x c hN hsS i (himm i))
  have L5 := pp_long N x c hn hN hsS hs0S hw y hy0 hsh
  have L6 : LR (fun _ => (1 : ℝ≥0∞)) 0 := LR.zero_rate 1 ENNReal.one_ne_top fun _ => le_rfl
  have Lall := (((((L1.add (L2.cmul (ENNReal.ofReal (3 * ctr N x c)) ENNReal.ofReal_ne_top)).add
    L3).add L4).add L5).add L6)
  have Lexp := LR.mono (fun T => exp_chain N x c θ hθd hdisp hord hident hN hx hsS hs0 hs0S hw hθ T)
    Lall
  unfold DetPolicy.avgCost OWMR.avgCost
  refine (LR.limsup Lexp).trans ?_
  -- the rates
  set I := ∫ w, max (((Finset.univ.sup w : ℝ≥0) : ℝ) - y) 0 ∂(Measure.pi fun _ : Fin N.L0 => ρ)
    with hI
  set infz := ⨅ z : ℝ, ∫ w, whLoss N.h N.p (z - ∑ j, (w j : ℝ)) ∂(Measure.pi fun _ : Fin N.L0 => ρ)
    with hinfz
  set Λ0 := ⨅ y, N.fL0 y with hΛ0
  set mean : Fin n → ℝ := fun i => ∫ x, (x : ℝ) ∂(N.marginal i) with hmean
  have hΛ00 : 0 ≤ Λ0 := Real.iInf_nonneg (fL0_nonneg N hN)
  have hmean0 : ∀ i, 0 ≤ mean i := fun i => integral_nonneg fun x => NNReal.coe_nonneg _
  have hI0 : 0 ≤ I := integral_nonneg fun w => le_max_right _ _
  have hinfz0 : 0 ≤ infz := Real.iInf_nonneg fun z => integral_nonneg fun w =>
    Asm.whLoss_nonneg _ _ _ hh.le hpp.le
  have hinfzle : infz ≤ Λ0 := arb_protected_newsvendor N hN hA (bset c)
  have hmeanρ : ∫ x, (x : ℝ) ∂ρ = ∑ i ∈ bset c, mean i := by
    rw [hρ, integral_map hg.aemeasurable measurable_coe_nnreal_real.aestronglyMeasurable]
    simp only [NNReal.coe_sum]
    rw [integral_finsetSum _ fun i _ => by
      have h1 := integrable_toReal_of_lintegral_ne_top
        (f := fun x : DemandVec n => ((x i : ℝ≥0) : ℝ≥0∞))
        ((measurable_pi_apply i).coe_nnreal_ennreal.aemeasurable) (hN.mean_lt_top i).ne
      simpa using h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hmean]
    unfold Network.marginal
    rw [integral_map (measurable_pi_apply i).aemeasurable
      measurable_coe_nnreal_real.aestronglyMeasurable]
  have htrig : ENNReal.ofReal (3 / 8 * N.h * y) + ENNReal.ofReal ((N.h + N.p) * (3 / 8))
      * ENNReal.ofReal I
      ≤ ENNReal.ofReal (3 / 4 * Λ0) + ∑ i ∈ bset c, ENNReal.ofReal (3 / 8 * N.h * mean i) := by
    have hhp1 : 1 + N.h / N.p ≤ 2 := by
      have := (div_le_one hpp).2 hp; linarith
    have key : 3 / 8 * N.h * y + (N.h + N.p) * (3 / 8) * I
        ≤ 3 / 4 * Λ0 + 3 / 8 * N.h * ∑ i ∈ bset c, mean i := by
      have e : 3 / 8 * N.h * y + (N.h + N.p) * (3 / 8) * I
          = 3 / 8 * ((N.h + N.p) * (N.h / (N.h + N.p) * y + I)) := by
        field_simp
      rw [e]
      have h1 := hy
      rw [hmeanρ] at h1
      have h2 : (1 + N.h / N.p) * infz ≤ 2 * Λ0 := by nlinarith
      nlinarith
    calc ENNReal.ofReal (3 / 8 * N.h * y) + ENNReal.ofReal ((N.h + N.p) * (3 / 8))
          * ENNReal.ofReal I
        = ENNReal.ofReal (3 / 8 * N.h * y + (N.h + N.p) * (3 / 8) * I) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
      _ ≤ ENNReal.ofReal (3 / 4 * Λ0 + 3 / 8 * N.h * ∑ i ∈ bset c, mean i) :=
          ENNReal.ofReal_le_ofReal key
      _ ≤ ENNReal.ofReal (3 / 4 * Λ0) + ENNReal.ofReal (3 / 8 * N.h * ∑ i ∈ bset c, mean i) :=
          ENNReal.ofReal_add_le
      _ = ENNReal.ofReal (3 / 4 * Λ0) + ∑ i ∈ bset c, ENNReal.ofReal (3 / 8 * N.h * mean i) := by
          rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun i _ => by
            have := hmean0 i; positivity]
  have hsup2 : ssAvgCost N.aggregate N.fL0 N.K0 c.s0 c.S0 + ENNReal.ofReal (3 / 4 * Λ0)
      ≤ 2 * N.J0 (conG m * N.K0) := by
    calc ssAvgCost N.aggregate N.fL0 N.K0 c.s0 c.S0 + ENNReal.ofReal (3 / 4 * Λ0)
        ≤ N.J0 (conG m * N.K0) + ENNReal.ofReal (N.h * a0) + ENNReal.ofReal (3 / 4 * Λ0) := by
          gcongr
      _ = N.J0 (conG m * N.K0) + ENNReal.ofReal (N.h * a0 + 3 / 4 * Λ0) := by
          rw [add_assoc, ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ N.J0 (conG m * N.K0) + ENNReal.ofReal (N.h * a0 + Λ0) := by
          gcongr; linarith
      _ ≤ N.J0 (conG m * N.K0) + N.J0 (conG m * N.K0) := add_le_add le_rfl hJ0a
      _ = 2 * N.J0 (conG m * N.K0) := (two_mul _).symm
  have hret2 : ∀ i, (if c.batch i = true then
        ssAvgCost (N.marginal i) (N.F i) (7 / 3 * N.K i) (c.s i) (c.S i)
          + ssAvgCost (N.marginal i) (fun y => N.h * max (c.S i - y) 0) 0 (c.s i) (c.S i)
        else ENNReal.ofReal (N.F i (c.S i) + N.K i))
      + (if c.batch i = true then
          min (ENNReal.ofReal (N.h * (3 / 8) * (c.S i - c.s i)))
            (ENNReal.ofReal ((N.h + N.p) * (c.S i - c.s i))
              * ssAvgCost (N.marginal i) (fun y => psi ((c.S i - y) / (c.S i - c.s i))) 0
                (c.s i) (c.S i))
          + ENNReal.ofReal (3 / 8 * N.h * mean i) else 0)
      ≤ ENNReal.ofReal (conB m) * N.J i (conZeta m * N.K i) := by
    intro i
    by_cases hb : c.batch i = true
    · rw [if_pos hb, if_pos hb, ← add_assoc]
      exact ((hret i).2 hb).2
    · rw [if_neg hb, if_neg hb, add_zero]
      exact ((hret i).1 (by simpa using hb)).2.2
  have e1 : ∑ i ∈ bset c, ENNReal.ofReal (3 / 8 * N.h * mean i)
      = ∑ i, (if c.batch i = true then ENNReal.ofReal (3 / 8 * N.h * mean i) else 0) :=
    Finset.sum_filter _ _
  have e2 : ∑ i ∈ bset c, min (ENNReal.ofReal (N.h * (3 / 8) * (c.S i - c.s i)))
      (ENNReal.ofReal ((N.h + N.p) * (c.S i - c.s i))
        * ssAvgCost (N.marginal i) (fun y => psi ((c.S i - y) / (c.S i - c.s i))) 0 (c.s i) (c.S i))
      = ∑ i, (if c.batch i = true then min (ENNReal.ofReal (N.h * (3 / 8) * (c.S i - c.s i)))
        (ENNReal.ofReal ((N.h + N.p) * (c.S i - c.s i))
          * ssAvgCost (N.marginal i) (fun y => psi ((c.S i - y) / (c.S i - c.s i))) 0
            (c.s i) (c.S i)) else 0) :=
    Finset.sum_filter _ _
  calc 0 + ENNReal.ofReal (3 * ctr N x c) * 0 + ssAvgCost N.aggregate N.fL0 N.K0 c.s0 c.S0
        + ∑ i, (if c.batch i = true then
            ssAvgCost (N.marginal i) (N.F i) (7 / 3 * N.K i) (c.s i) (c.S i)
              + ssAvgCost (N.marginal i) (fun y => N.h * max (c.S i - y) 0) 0 (c.s i) (c.S i)
            else ENNReal.ofReal (N.F i (c.S i) + N.K i))
        + (ENNReal.ofReal (3 / 8 * N.h * y) + ENNReal.ofReal ((N.h + N.p) * (3 / 8)) * ENNReal.ofReal I
          + ∑ i ∈ bset c, min (ENNReal.ofReal (N.h * (3 / 8) * (c.S i - c.s i)))
            (ENNReal.ofReal ((N.h + N.p) * (c.S i - c.s i))
              * ssAvgCost (N.marginal i) (fun y => psi ((c.S i - y) / (c.S i - c.s i))) 0
                (c.s i) (c.S i))) + 0
      ≤ ssAvgCost N.aggregate N.fL0 N.K0 c.s0 c.S0
        + ∑ i, (if c.batch i = true then
            ssAvgCost (N.marginal i) (N.F i) (7 / 3 * N.K i) (c.s i) (c.S i)
              + ssAvgCost (N.marginal i) (fun y => N.h * max (c.S i - y) 0) 0 (c.s i) (c.S i)
            else ENNReal.ofReal (N.F i (c.S i) + N.K i))
        + (ENNReal.ofReal (3 / 4 * Λ0) + ∑ i ∈ bset c, ENNReal.ofReal (3 / 8 * N.h * mean i)
          + ∑ i ∈ bset c, min (ENNReal.ofReal (N.h * (3 / 8) * (c.S i - c.s i)))
            (ENNReal.ofReal ((N.h + N.p) * (c.S i - c.s i))
              * ssAvgCost (N.marginal i) (fun y => psi ((c.S i - y) / (c.S i - c.s i))) 0
                (c.s i) (c.S i))) := by
        simp only [mul_zero, zero_add, add_zero]
        gcongr
    _ = (ssAvgCost N.aggregate N.fL0 N.K0 c.s0 c.S0 + ENNReal.ofReal (3 / 4 * Λ0))
        + ∑ i, ((if c.batch i = true then
            ssAvgCost (N.marginal i) (N.F i) (7 / 3 * N.K i) (c.s i) (c.S i)
              + ssAvgCost (N.marginal i) (fun y => N.h * max (c.S i - y) 0) 0 (c.s i) (c.S i)
            else ENNReal.ofReal (N.F i (c.S i) + N.K i))
          + (if c.batch i = true then
            min (ENNReal.ofReal (N.h * (3 / 8) * (c.S i - c.s i)))
              (ENNReal.ofReal ((N.h + N.p) * (c.S i - c.s i))
                * ssAvgCost (N.marginal i) (fun y => psi ((c.S i - y) / (c.S i - c.s i))) 0
                  (c.s i) (c.S i))
            + ENNReal.ofReal (3 / 8 * N.h * mean i) else 0)) := by
        rw [e1, e2]
        have e3 : ∀ i, (if c.batch i = true then
            min (ENNReal.ofReal (N.h * (3 / 8) * (c.S i - c.s i)))
              (ENNReal.ofReal ((N.h + N.p) * (c.S i - c.s i))
                * ssAvgCost (N.marginal i) (fun y => psi ((c.S i - y) / (c.S i - c.s i))) 0
                  (c.s i) (c.S i))
            + ENNReal.ofReal (3 / 8 * N.h * mean i) else 0)
            = (if c.batch i = true then ENNReal.ofReal (3 / 8 * N.h * mean i) else 0)
              + (if c.batch i = true then min (ENNReal.ofReal (N.h * (3 / 8) * (c.S i - c.s i)))
                (ENNReal.ofReal ((N.h + N.p) * (c.S i - c.s i))
                  * ssAvgCost (N.marginal i) (fun y => psi ((c.S i - y) / (c.S i - c.s i))) 0
                    (c.s i) (c.S i)) else 0) := fun i => by
          split_ifs <;> simp [add_comm]
        simp only [e3, Finset.sum_add_distrib]
        ring
    _ ≤ 2 * N.J0 (conG m * N.K0) + ∑ i, ENNReal.ofReal (conB m) * N.J i (conZeta m * N.K i) :=
        add_le_add hsup2 (Finset.sum_le_sum fun i _ => hret2 i)
    _ = 2 * N.J0 (conG m * N.K0) + ENNReal.ofReal (conB m) * ∑ i, N.J i (conZeta m * N.K i) := by
        rw [Finset.mul_sum]

end Part16

end
