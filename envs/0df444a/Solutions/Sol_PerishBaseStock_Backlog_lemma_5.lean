-- Prove2me | solution 1 for PerishBaseStock.Backlog.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T19:51:53.704498+00:00
-- url     : https://prove2.me/submissions/aef49df7-371c-4b7b-b6b7-7172d915f975

import Theorems.Thm_PerishBaseStock_Backlog_ec_29
import Theorems.Thm_PerishBaseStock_Backlog_ec_30

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

namespace PB7H
open PerishBaseStock.Backlog LostSalesOrderUpTo.Asymptotic CappedBaseStock

theorem meas_sum (k : ℕ) :
    Measurable (fun d : DemandPath => ∑ i ∈ Finset.range (k + 1), d i) := by fun_prop

instance isProb_lead (P : DemandLaw) (k : ℕ) : IsProbabilityMeasure (leadTimeLaw P k) :=
  Measure.isProbabilityMeasure_map (meas_sum k).aemeasurable

theorem coord_integrable (P : DemandLaw) (i : ℕ) :
    Integrable (fun d : DemandPath => ((d i : ℝ≥0) : ℝ)) (demandPathLaw P) := by
  have h : (demandPathLaw P).map (fun d => d i) = P.law :=
    Measure.infinitePi_map_eval _ i
  have hf := P.finiteMean
  rw [← h] at hf
  exact (integrable_map_measure (by fun_prop) (measurable_pi_apply i).aemeasurable).1 hf

theorem lead_integrable (P : DemandLaw) (k : ℕ) :
    Integrable (fun x : ℝ≥0 => (x : ℝ)) (leadTimeLaw P k) := by
  unfold leadTimeLaw
  refine (integrable_map_measure (by fun_prop) (meas_sum k).aemeasurable).2 ?_
  have : ((fun x : ℝ≥0 => (x : ℝ)) ∘ fun d : DemandPath => ∑ i ∈ Finset.range (k + 1), d i) =
      fun d => ∑ i ∈ Finset.range (k + 1), ((d i : ℝ≥0) : ℝ) := by
    ext d; simp
  rw [this]
  exact integrable_finsetSum _ fun i _ => coord_integrable P i

section general
variable (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]

theorem eh_int (S : ℝ≥0) : Integrable (fun x : ℝ≥0 => max ((S : ℝ) - x) 0) μ := by
  refine Integrable.of_bound (by fun_prop) (S : ℝ) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith [x.2]) S.2

theorem es_int (hμ : Integrable (fun x : ℝ≥0 => (x : ℝ)) μ) (S : ℝ≥0) :
    Integrable (fun x : ℝ≥0 => max ((x : ℝ) - S) 0) μ := by
  refine hμ.mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith [S.2]) x.2

theorem eh_nonneg (S : ℝ≥0) : 0 ≤ expectedHolding μ S :=
  integral_nonneg fun _ => le_max_right _ _

theorem es_nonneg (S : ℝ≥0) : 0 ≤ expectedShortfall μ S :=
  integral_nonneg fun _ => le_max_right _ _

theorem eh_zero : expectedHolding μ 0 = 0 := by
  unfold expectedHolding
  have : (fun x : ℝ≥0 => max (((0 : ℝ≥0) : ℝ) - x) 0) = fun _ => 0 := by
    ext x; simp [x.2]
  rw [this, integral_zero]

theorem eh_ge (hμ : Integrable (fun x : ℝ≥0 => (x : ℝ)) μ) (S : ℝ≥0) :
    (S : ℝ) - ∫ x : ℝ≥0, (x : ℝ) ∂μ ≤ expectedHolding μ S := by
  have h1 : ∫ x : ℝ≥0, ((S : ℝ) - x) ∂μ = (S : ℝ) - ∫ x : ℝ≥0, (x : ℝ) ∂μ := by
    rw [integral_sub (integrable_const _) hμ]; simp
  rw [← h1]
  exact integral_mono ((integrable_const _).sub hμ) (eh_int μ S) fun x => le_max_left _ _

theorem eh_mono {S S' : ℝ≥0} (h : S ≤ S') : expectedHolding μ S ≤ expectedHolding μ S' :=
  integral_mono (eh_int μ S) (eh_int μ S') fun x =>
    max_le_max (by have : (S : ℝ) ≤ S' := h; linarith) le_rfl

theorem eh_lip (S S' : ℝ≥0) :
    expectedHolding μ S' - expectedHolding μ S ≤ max ((S' : ℝ) - S) 0 := by
  unfold expectedHolding
  rw [← integral_sub (eh_int μ S') (eh_int μ S)]
  have : ∫ _x : ℝ≥0, max ((S' : ℝ) - S) 0 ∂μ = max ((S' : ℝ) - S) 0 := by simp
  rw [← this]
  refine integral_mono ((eh_int μ S').sub (eh_int μ S)) (integrable_const _) fun x => ?_
  simp only
  rcases le_total ((S' : ℝ) - x) 0 with h1 | h1 <;> rcases le_total ((S : ℝ) - x) 0 with h2 | h2 <;>
    simp only [max_eq_right h1, max_eq_left h1, max_eq_right h2, max_eq_left h2] <;>
    first
    | (rcases le_total ((S' : ℝ) - S) 0 with h3 | h3 <;>
        simp only [max_eq_right h3, max_eq_left h3] <;> linarith)

theorem es_lip (hμ : Integrable (fun x : ℝ≥0 => (x : ℝ)) μ) (S S' : ℝ≥0) :
    expectedShortfall μ S' - expectedShortfall μ S ≤ max ((S : ℝ) - S') 0 := by
  unfold expectedShortfall
  rw [← integral_sub (es_int μ hμ S') (es_int μ hμ S)]
  have : ∫ _x : ℝ≥0, max ((S : ℝ) - S') 0 ∂μ = max ((S : ℝ) - S') 0 := by simp
  rw [← this]
  refine integral_mono ((es_int μ hμ S').sub (es_int μ hμ S)) (integrable_const _) fun x => ?_
  simp only
  rcases le_total ((x : ℝ) - S') 0 with h1 | h1 <;> rcases le_total ((x : ℝ) - S) 0 with h2 | h2 <;>
    simp only [max_eq_right h1, max_eq_left h1, max_eq_right h2, max_eq_left h2] <;>
    first
    | (rcases le_total ((S : ℝ) - S') 0 with h3 | h3 <;>
        simp only [max_eq_right h3, max_eq_left h3] <;> linarith)

end general

end PB7H

namespace PB7P
open PerishBaseStock.Backlog

/-- real one-period cost -/
def rc (c : Params) (π : Policy c) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ :=
  c.h * max (levelAt c π d t c.m - d t) 0 + c.b * max ((d t : ℝ) - levelAt c π d t c.m) 0 +
    c.θ * outdatedAt c π d t

theorem costAt_eq (c : Params) (π : Policy c) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    costAt c π d t = ENNReal.ofReal (rc c π d t) := rfl

/-- the per-period lower-bound integrand of (EC.33) -/
def psi (c : Params) (y a b : ℝ) : ℝ :=
  c.h * max (y - a) 0 + c.b * max (a - y) 0 + (c.θ - c.h * c.L) / ((c.m : ℝ) + c.L) * max (y - b) 0

def X1 (c : Params) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico t (t + c.L + 1), (d i : ℝ)

def Xm (c : Params) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico t (t + c.m + c.L), (d i : ℝ)

theorem outdated_nonneg (c : Params) (π : Policy c) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    0 ≤ outdatedAt c π d t := le_max_right _ _

theorem double_count (o : ℕ → ℝ) (ho : ∀ i, 0 ≤ o i) (T k : ℕ) :
    ∑ t ∈ Finset.range T, ∑ i ∈ Finset.Ico t (t + k), o i ≤
      k * ∑ i ∈ Finset.range (T + k - 1), o i := by
  have h1 : ∀ t, ∑ i ∈ Finset.Ico t (t + k), o i = ∑ j ∈ Finset.range k, o (t + j) := by
    intro t; rw [Finset.sum_Ico_eq_sum_range]; simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ j ∈ Finset.range k, ∑ t ∈ Finset.range T, o (t + j) ≤
      ∑ i ∈ Finset.range (T + k - 1), o i := by
    intro j hj
    rw [Finset.mem_range] at hj
    have : ∑ t ∈ Finset.range T, o (t + j) = ∑ i ∈ Finset.Ico j (j + T), o i := by
      rw [Finset.sum_Ico_eq_sum_range]; simp [add_comm]
    rw [this]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi; simp only [Finset.mem_Ico, Finset.mem_range] at hi ⊢; omega
    · intro i _ _; exact ho i
  calc ∑ j ∈ Finset.range k, ∑ t ∈ Finset.range T, o (t + j)
      ≤ ∑ j ∈ Finset.range k, ∑ i ∈ Finset.range (T + k - 1), o i := Finset.sum_le_sum h2
    _ = _ := by simp

/-- (EC.33), zero-based: for any policy and demand path. -/
theorem ec33 (c : Params) (hc : c.Standing) (π : Policy c) (d : CappedBaseStock.DemandPath)
    (T : ℕ) :
    ∑ t ∈ Finset.range T, psi c (levelAt c π d t (c.m + c.L)) (X1 c d t) (Xm c d t) ≤
      ∑ t ∈ Finset.range (T + c.m + c.L), rc c π d t := by
  obtain ⟨hm1, hh, hb, hθ⟩ := hc
  set o := outdatedAt c π d with ho_def
  have ho : ∀ i, 0 ≤ o i := outdated_nonneg c π d
  have hL0 : (0 : ℝ) ≤ c.L := Nat.cast_nonneg _
  have hmr : (1 : ℝ) ≤ c.m := by exact_mod_cast hm1
  have hpos : (0 : ℝ) < (c.m : ℝ) + c.L := by positivity
  set x := fun t => levelAt c π d t (c.m + c.L)
  set G : ℕ → ℝ := fun s => c.h * max (x s - X1 c d s) 0 + c.b * max (X1 c d s - x s) 0
  set hbp : ℕ → ℝ := fun t => c.h * max (levelAt c π d t c.m - d t) 0 +
    c.b * max ((d t : ℝ) - levelAt c π d t c.m) 0
  have hbp0 : ∀ t, 0 ≤ hbp t := fun t => by positivity
  have hG0 : ∀ t, 0 ≤ G t := fun t => by positivity
  -- (EC.31)
  have ec31 : ∀ s, G s - c.h * ∑ i ∈ Finset.Ico s (s + c.L), o i ≤ hbp (s + c.L) := by
    intro s
    have e29 := PerishBaseStock.Backlog.ec_29 c hm1 π d s
    have hO : 0 ≤ ∑ i ∈ Finset.Ico s (s + c.L), o i := Finset.sum_nonneg fun i _ => ho i
    have hX1 : X1 c d s = ∑ i ∈ Finset.Ico s (s + c.L), (d i : ℝ) + d (s + c.L) := by
      unfold X1; rw [show s + c.L + 1 = (s + c.L) + 1 by ring, Finset.sum_Ico_succ_top (by omega)]
    simp only [hbp, G]
    rw [e29, hX1]
    set A := ∑ i ∈ Finset.Ico s (s + c.L), (d i : ℝ)
    set O := ∑ i ∈ Finset.Ico s (s + c.L), o i
    set y := x s
    have k1 : max (y - (A + d (s + c.L))) 0 - O ≤ max (y - A - O - d (s + c.L)) 0 := by
      rcases le_total (y - (A + d (s + c.L))) 0 with h | h
      · rw [max_eq_right h]; linarith [le_max_right (y - A - O - d (s + c.L)) 0]
      · rw [max_eq_left h]; linarith [le_max_left (y - A - O - d (s + c.L)) 0]
    have k2 : max (A + d (s + c.L) - y) 0 ≤ max ((d (s + c.L) : ℝ) - (y - A - O)) 0 := by
      apply max_le_max _ le_rfl; linarith
    nlinarith [mul_le_mul_of_nonneg_left k1 hh.le, mul_le_mul_of_nonneg_left k2 hb.le]
  -- split the total cost
  have hsplit : ∑ t ∈ Finset.range (T + c.m + c.L), rc c π d t =
      ∑ t ∈ Finset.range (T + c.m + c.L), hbp t + c.θ * ∑ t ∈ Finset.range (T + c.m + c.L), o t := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]; rfl
  have hdrop : ∑ s ∈ Finset.range (T + c.m), hbp (s + c.L) ≤
      ∑ t ∈ Finset.range (T + c.m + c.L), hbp t := by
    have e : ∑ t ∈ Finset.range (T + c.m + c.L), hbp t =
        ∑ t ∈ Finset.range c.L, hbp t + ∑ s ∈ Finset.range (T + c.m), hbp (c.L + s) := by
      rw [show T + c.m + c.L = c.L + (T + c.m) by ring]; exact Finset.sum_range_add _ _ _
    rw [e]
    have : 0 ≤ ∑ t ∈ Finset.range c.L, hbp t := Finset.sum_nonneg fun t _ => hbp0 t
    have e2 : ∑ s ∈ Finset.range (T + c.m), hbp (c.L + s) =
        ∑ s ∈ Finset.range (T + c.m), hbp (s + c.L) := by simp_rw [add_comm c.L]
    linarith
  have hdc1 := double_count o ho (T + c.m) c.L
  have hdc2 := double_count o ho T (c.m + c.L)
  have hidx : T + c.m + c.L - 1 = T + (c.m + c.L) - 1 := by ring_nf
  rw [show T + c.m + c.L - 1 = T + (c.m + c.L) - 1 by omega] at hdc1
  set Osum := ∑ i ∈ Finset.range (T + (c.m + c.L) - 1), o i
  have hOs : 0 ≤ Osum := Finset.sum_nonneg fun i _ => ho i
  have hOfull : Osum ≤ ∑ t ∈ Finset.range (T + c.m + c.L), o t := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
    · intro i _ _; exact ho i
  have e30 : ∑ t ∈ Finset.range T, max (x t - Xm c d t) 0 ≤
      ∑ t ∈ Finset.range T, ∑ i ∈ Finset.Ico t (t + (c.m + c.L)), o i := by
    apply Finset.sum_le_sum; intro t _
    have := PerishBaseStock.Backlog.ec_30 c hm1 π d t
    rw [show t + (c.m + c.L) = t + c.m + c.L by ring]; exact this
  have hsumG : ∑ t ∈ Finset.range T, G t ≤ ∑ s ∈ Finset.range (T + c.m), G s := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
    · intro i _ _; exact hG0 i
  have h31sum : ∑ s ∈ Finset.range (T + c.m), G s - c.h * (c.L * Osum) ≤
      ∑ s ∈ Finset.range (T + c.m), hbp (s + c.L) := by
    have := Finset.sum_le_sum fun s (_ : s ∈ Finset.range (T + c.m)) => ec31 s
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at this
    nlinarith [mul_le_mul_of_nonneg_left hdc1 hh.le]
  have hα : (c.θ - c.h * c.L) / ((c.m : ℝ) + c.L) *
      ∑ t ∈ Finset.range T, max (x t - Xm c d t) 0 ≤ (c.θ - c.h * c.L) * Osum := by
    have hθ' : 0 ≤ c.θ - c.h * c.L := by linarith
    have : ∑ t ∈ Finset.range T, max (x t - Xm c d t) 0 ≤ ((c.m : ℝ) + c.L) * Osum := by
      have := e30.trans hdc2; push_cast at this; linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    nlinarith [mul_le_mul_of_nonneg_left this hθ']
  have hθ0 : 0 ≤ c.θ := le_trans (by positivity) hθ
  have hpsi : ∑ t ∈ Finset.range T, psi c (x t) (X1 c d t) (Xm c d t) =
      ∑ t ∈ Finset.range T, G t + (c.θ - c.h * c.L) / ((c.m : ℝ) + c.L) *
        ∑ t ∈ Finset.range T, max (x t - Xm c d t) 0 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]; rfl
  rw [hpsi, hsplit]
  nlinarith [mul_le_mul_of_nonneg_left hOfull hθ0]

end PB7P

namespace PB7E
open PerishBaseStock.Backlog LostSalesOrderUpTo.Asymptotic CappedBaseStock PB7H PB7P

section meas
variable (c : Params)

theorem meas_level (i : ℕ) : Measurable (fun p : State c × ℝ => level c p.1 p.2 i) := by
  unfold level orderUpTo
  split_ifs
  · exact ((measurable_stateCoord c _).comp measurable_fst).add measurable_snd
  · exact (measurable_stateCoord c _).comp measurable_fst

theorem meas_outdated : Measurable (fun p : State c × ℝ × ℝ => outdated c p.1 p.2.1 p.2.2) := by
  unfold outdated
  exact (((meas_level c 1).comp (measurable_fst.prodMk measurable_snd.fst)).sub
    measurable_snd.snd).max measurable_const

theorem meas_next : Measurable (fun p : State c × ℝ × ℝ => next c p.1 p.2.1 p.2.2) :=
  measurable_pi_lambda _ fun _ =>
    (((meas_level c _).comp (measurable_fst.prodMk measurable_snd.fst)).sub
      measurable_snd.snd).sub (meas_outdated c)

variable (π : Policy c)

theorem meas_traj (t : ℕ) : Measurable (fun d : DemandPath => traj c π d t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hq : Measurable (fun d : DemandPath => ((π.φ t (traj c π d t) : ℝ≥0) : ℝ)) :=
      ((π.measurable_φ t).comp ih).coe_nnreal_real
    have hd : Measurable (fun d : DemandPath => ((d t : ℝ≥0) : ℝ)) :=
      (measurable_pi_apply t).coe_nnreal_real
    exact (meas_next c).comp (ih.prodMk (hq.prodMk hd))

theorem meas_order (t : ℕ) : Measurable (fun d : DemandPath => orderAt c π d t) :=
  ((π.measurable_φ t).comp (meas_traj c π t)).coe_nnreal_real

theorem meas_levelAt (t i : ℕ) : Measurable (fun d : DemandPath => levelAt c π d t i) :=
  (meas_level c i).comp ((meas_traj c π t).prodMk (meas_order c π t))

theorem meas_outdatedAt (t : ℕ) : Measurable (fun d : DemandPath => outdatedAt c π d t) :=
  (meas_outdated c).comp ((meas_traj c π t).prodMk ((meas_order c π t).prodMk
    (measurable_pi_apply t).coe_nnreal_real))

theorem meas_rc (t : ℕ) : Measurable (fun d : DemandPath => rc c π d t) := by
  unfold rc
  have h1 := meas_levelAt c π t c.m
  have h2 : Measurable (fun d : DemandPath => ((d t : ℝ≥0) : ℝ)) :=
    (measurable_pi_apply t).coe_nnreal_real
  have h3 := meas_outdatedAt c π t
  fun_prop

theorem meas_X1 (t : ℕ) : Measurable (fun d : DemandPath => X1 c d t) := by
  unfold X1; fun_prop

theorem meas_Xm (t : ℕ) : Measurable (fun d : DemandPath => Xm c d t) := by
  unfold Xm; fun_prop

theorem meas_psi : Measurable (fun p : ℝ × ℝ × ℝ => psi c p.1 p.2.1 p.2.2) := by
  unfold psi; fun_prop

end meas

theorem psi_nonneg (c : Params) (hc : c.Standing) (y a b : ℝ) : 0 ≤ psi c y a b := by
  obtain ⟨hm1, hh, hb, hθ⟩ := hc
  have hmr : (1 : ℝ) ≤ c.m := by exact_mod_cast hm1
  have hL0 : (0 : ℝ) ≤ c.L := Nat.cast_nonneg _
  unfold psi
  have : 0 ≤ (c.θ - c.h * c.L) / ((c.m : ℝ) + c.L) := div_nonneg (by linarith) (by positivity)
  positivity

theorem rc_nonneg (c : Params) (hc : c.Standing) (π : Policy c) (d : DemandPath) (t : ℕ) :
    0 ≤ rc c π d t := by
  obtain ⟨hm1, hh, hb, hθ⟩ := hc
  have hL0 : (0 : ℝ) ≤ c.L := Nat.cast_nonneg _
  have hθ0 : 0 ≤ c.θ := le_trans (by positivity) hθ
  unfold rc
  have := outdated_nonneg c π d t
  positivity

/-- ratio limit used for the long-run average -/
theorem ratio_tendsto (k : ℕ) (K : ℝ≥0∞) (hK : K ≠ ⊤) :
    Tendsto (fun N : ℕ => (N : ℝ≥0∞)⁻¹ * (((N - k : ℕ) : ℝ≥0∞) * K)) atTop (𝓝 K) := by
  have hr : Tendsto (fun N : ℕ => (1 : ℝ) - (k : ℝ) / N) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ))
  have h1 : Tendsto (fun N : ℕ => ENNReal.ofReal (1 - (k : ℝ) / N)) atTop (𝓝 1) := by
    simpa using ENNReal.tendsto_ofReal hr
  have heq : ∀ᶠ N : ℕ in atTop, ENNReal.ofReal (1 - (k : ℝ) / N) =
      (N : ℝ≥0∞)⁻¹ * ((N - k : ℕ) : ℝ≥0∞) := by
    filter_upwards [eventually_ge_atTop (k + 1)] with N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have : (1 : ℝ) - (k : ℝ) / N = ((N - k : ℕ) : ℝ) / N := by
      rw [Nat.cast_sub (by omega)]; field_simp
    rw [this, ENNReal.ofReal_div_of_pos hNpos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
      div_eq_mul_inv, mul_comm]
  have h2 := ENNReal.Tendsto.mul_const (h1.congr' heq) (b := K) (Or.inr hK)
  simp only [one_mul] at h2
  refine h2.congr fun N => ?_
  ring

/-- Lower-bound engine: if every period's (EC.33) integrand has expectation at least `K`,
the long-run average cost is at least `K`. -/
theorem engine (P : DemandLaw) (c : Params) (hc : c.Standing) (π : Policy c) (K : ℝ)
    (h : ∀ t, ENNReal.ofReal K ≤ ∫⁻ d, ENNReal.ofReal
      (psi c (levelAt c π d t (c.m + c.L)) (X1 c d t) (Xm c d t)) ∂demandPathLaw P) :
    ENNReal.ofReal K ≤ policyCost P c π := by
  set ν := demandPathLaw P
  have hbound : ∀ N : ℕ, ((N - (c.m + c.L) : ℕ) : ℝ≥0∞) * ENNReal.ofReal K ≤
      ∑ t ∈ Finset.range N, ∫⁻ d, costAt c π d t ∂ν := by
    intro N
    rcases lt_or_ge N (c.m + c.L) with hN | hN
    · rw [Nat.sub_eq_zero_of_le hN.le]; simp
    set T := N - (c.m + c.L)
    have hNT : N = T + c.m + c.L := by omega
    rw [← lintegral_finsetSum' _ (fun t _ => ?_)]
    swap
    · exact ((meas_rc c π t).ennreal_ofReal).aemeasurable
    simp_rw [costAt_eq]
    have hpt : ∀ d, ∑ t ∈ Finset.range T, ENNReal.ofReal
        (psi c (levelAt c π d t (c.m + c.L)) (X1 c d t) (Xm c d t)) ≤
        ∑ t ∈ Finset.range N, ENNReal.ofReal (rc c π d t) := by
      intro d
      rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ => psi_nonneg c hc _ _ _),
        ← ENNReal.ofReal_sum_of_nonneg (fun t _ => rc_nonneg c hc π d t), hNT]
      exact ENNReal.ofReal_le_ofReal (ec33 c hc π d T)
    calc ((T : ℕ) : ℝ≥0∞) * ENNReal.ofReal K
        = ∑ t ∈ Finset.range T, ENNReal.ofReal K := by simp
      _ ≤ ∑ t ∈ Finset.range T, ∫⁻ d, ENNReal.ofReal
          (psi c (levelAt c π d t (c.m + c.L)) (X1 c d t) (Xm c d t)) ∂ν :=
          Finset.sum_le_sum fun t _ => h t
      _ = ∫⁻ d, ∑ t ∈ Finset.range T, ENNReal.ofReal
          (psi c (levelAt c π d t (c.m + c.L)) (X1 c d t) (Xm c d t)) ∂ν := by
          rw [lintegral_finsetSum' _ (fun t _ => ?_)]
          exact (((meas_psi c).comp ((meas_levelAt c π t _).prodMk
            ((meas_X1 c t).prodMk (meas_Xm c t)))).ennreal_ofReal).aemeasurable
      _ ≤ _ := lintegral_mono hpt
  unfold PerishBaseStock.Backlog.policyCost
  calc ENNReal.ofReal K = limsup (fun N : ℕ => (N : ℝ≥0∞)⁻¹ *
        (((N - (c.m + c.L) : ℕ) : ℝ≥0∞) * ENNReal.ofReal K)) atTop :=
        ((ratio_tendsto _ _ ENNReal.ofReal_ne_top).limsup_eq).symm
    _ ≤ _ := limsup_le_limsup (Eventually.of_forall fun N => mul_le_mul_right (hbound N) _)

/-- shift invariance of the i.i.d. demand law -/
theorem shift_map (P : DemandLaw) (t : ℕ) :
    (demandPathLaw P).map (fun d : DemandPath => fun i => d (t + i)) = demandPathLaw P := by
  unfold demandPathLaw
  exact Measure.map_infinitePi_infinitePi_of_inj (fun a b h => by simpa using h)

theorem sum_Ico_shift (d : DemandPath) (t k : ℕ) :
    ∑ i ∈ Finset.Ico t (t + k), ((d i : ℝ≥0) : ℝ) = ∑ i ∈ Finset.range k, ((d (t + i) : ℝ≥0) : ℝ) := by
  rw [Finset.sum_Ico_eq_sum_range]; simp

theorem integrable_sum_coord (P : DemandLaw) (k : ℕ) :
    Integrable (fun d : DemandPath => ∑ i ∈ Finset.range k, ((d i : ℝ≥0) : ℝ)) (demandPathLaw P) :=
  integrable_finsetSum _ fun i _ => coord_integrable P i

theorem eh_as (P : DemandLaw) (k : ℕ) (S : ℝ≥0) :
    expectedHolding (leadTimeLaw P k) S =
      ∫ d, max ((S : ℝ) - ∑ i ∈ Finset.range (k + 1), ((d i : ℝ≥0) : ℝ)) 0 ∂demandPathLaw P := by
  unfold expectedHolding leadTimeLaw
  rw [integral_map (meas_sum k).aemeasurable (by fun_prop)]
  simp

theorem es_as (P : DemandLaw) (k : ℕ) (S : ℝ≥0) :
    expectedShortfall (leadTimeLaw P k) S =
      ∫ d, max (∑ i ∈ Finset.range (k + 1), ((d i : ℝ≥0) : ℝ) - S) 0 ∂demandPathLaw P := by
  unfold expectedShortfall leadTimeLaw
  rw [integral_map (meas_sum k).aemeasurable (by fun_prop)]
  simp

/-- The expectation of the (EC.33) integrand at a fixed level `S` is `C̃^L(S)`. -/
theorem meas_sumR (k : ℕ) :
    Measurable (fun d : DemandPath => ∑ i ∈ Finset.range k, ((d i : ℝ≥0) : ℝ)) :=
  Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).coe_nnreal_real

theorem psi_expect (P : DemandLaw) (c : Params) (hc : c.Standing) (S : ℝ≥0) (t : ℕ) :
    ENNReal.ofReal (heuristicCost P c S) ≤
      ∫⁻ d, ENNReal.ofReal (psi c S (X1 c d t) (Xm c d t)) ∂demandPathLaw P := by
  set F : DemandPath → ℝ := fun d => psi c S (∑ i ∈ Finset.range (c.L + 1), ((d i : ℝ≥0) : ℝ))
    (∑ i ∈ Finset.range (c.m + c.L), ((d i : ℝ≥0) : ℝ))
  have hFm : Measurable F := by
    simp only [F]; unfold psi
    have := meas_sumR (c.L + 1); have := meas_sumR (c.m + c.L); fun_prop
  have hshm : Measurable (fun d : DemandPath => fun i => d (t + i)) := by fun_prop
  have hshift : ∫⁻ d, ENNReal.ofReal (psi c S (X1 c d t) (Xm c d t)) ∂demandPathLaw P =
      ∫⁻ d, ENNReal.ofReal (F d) ∂demandPathLaw P := by
    calc _ = ∫⁻ d, ENNReal.ofReal (F (fun i => d (t + i))) ∂demandPathLaw P := by
          congr 1; ext d
          simp only [F, X1, Xm]
          rw [show t + c.L + 1 = t + (c.L + 1) by ring, show t + c.m + c.L = t + (c.m + c.L) by ring,
            sum_Ico_shift, sum_Ico_shift]
      _ = ∫⁻ d, ENNReal.ofReal (F d) ∂((demandPathLaw P).map (fun d : DemandPath =>
            fun i => d (t + i))) := (lintegral_map hFm.ennreal_ofReal hshm).symm
      _ = _ := by rw [shift_map]
  rw [hshift]
  set f1 : DemandPath → ℝ := fun d => max ((S : ℝ) - ∑ i ∈ Finset.range (c.L + 1), ((d i : ℝ≥0) : ℝ)) 0
  set f2 : DemandPath → ℝ := fun d => max (∑ i ∈ Finset.range (c.L + 1), ((d i : ℝ≥0) : ℝ) - S) 0
  set f3 : DemandPath → ℝ := fun d => max ((S : ℝ) - ∑ i ∈ Finset.range (c.m + c.L), ((d i : ℝ≥0) : ℝ)) 0
  have i1 : Integrable f1 (demandPathLaw P) := by
    refine Integrable.of_bound ((measurable_const.sub (meas_sumR _)).max
      measurable_const).aestronglyMeasurable (S : ℝ) (ae_of_all _ fun d => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    have : (0 : ℝ) ≤ ∑ i ∈ Finset.range (c.L + 1), ((d i : ℝ≥0) : ℝ) :=
      Finset.sum_nonneg fun i _ => NNReal.coe_nonneg _
    exact max_le (by linarith) S.2
  have i3 : Integrable f3 (demandPathLaw P) := by
    refine Integrable.of_bound ((measurable_const.sub (meas_sumR _)).max
      measurable_const).aestronglyMeasurable (S : ℝ) (ae_of_all _ fun d => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    have : (0 : ℝ) ≤ ∑ i ∈ Finset.range (c.m + c.L), ((d i : ℝ≥0) : ℝ) :=
      Finset.sum_nonneg fun i _ => NNReal.coe_nonneg _
    exact max_le (by linarith) S.2
  have i2 : Integrable f2 (demandPathLaw P) := by
    refine (integrable_sum_coord P (c.L + 1)).mono' (((meas_sumR _).sub measurable_const).max
      measurable_const).aestronglyMeasurable (ae_of_all _ fun d => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [S.2]) (Finset.sum_nonneg fun i _ => NNReal.coe_nonneg _)
  set α : ℝ := (c.θ - c.h * c.L) / ((c.m : ℝ) + c.L)
  have hA : Integrable (fun d => c.h * f1 d + c.b * f2 d) (demandPathLaw P) :=
    (i1.const_mul _).add (i2.const_mul _)
  have hB : Integrable (fun d => α * f3 d) (demandPathLaw P) := i3.const_mul _
  have hFeq : F = fun d => (c.h * f1 d + c.b * f2 d) + α * f3 d := rfl
  have hFi : Integrable F (demandPathLaw P) := by rw [hFeq]; exact hA.add hB
  have hFint : ∫ d, F d ∂demandPathLaw P = heuristicCost P c S := by
    rw [hFeq, integral_add hA hB, integral_add (i1.const_mul _) (i2.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul]
    unfold heuristicCost
    rw [eh_as, es_as, eh_as]
    have : c.m + c.L - 1 + 1 = c.m + c.L := by have := hc.1; omega
    rw [this]
  rw [← hFint, ofReal_integral_eq_lintegral_ofReal hFi
    (ae_of_all _ fun d => psi_nonneg c hc _ _ _)]

/-- `psi` at a negative level dominates `psi` at level zero. -/
theorem psi_pos_part (c : Params) (y a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c.Standing) :
    psi c (max y 0) a b ≤ psi c y a b := by
  rcases le_total y 0 with h | h
  · rw [max_eq_right h]
    unfold psi
    have h1 : max (0 - a) 0 = 0 := max_eq_right (by linarith)
    have h2 : max (0 - b) 0 = 0 := max_eq_right (by linarith)
    have h3 : max (y - a) 0 = 0 := max_eq_right (by linarith)
    have h4 : max (y - b) 0 = 0 := max_eq_right (by linarith)
    rw [h1, h2, h3, h4]
    have : max (a - 0) 0 ≤ max (a - y) 0 := max_le_max (by linarith) le_rfl
    nlinarith [hc.2.2.1]
  · rw [max_eq_left h]

end PB7E

namespace PB7B
open PerishBaseStock.Backlog LostSalesOrderUpTo.Asymptotic CappedBaseStock PB7H PB7P PB7E

theorem step (c : Params) (π : Policy c) (d : DemandPath) (t i : ℕ)
    (hi1 : 1 ≤ i) (hi2 : i ≤ c.m + c.L - 1) :
    levelAt c π d (t + 1) i = levelAt c π d t (i + 1) - (d t : ℝ) - outdatedAt c π d t := by
  have hne : i ≠ c.m + c.L := by omega
  simp only [levelAt, level, if_neg hne, stateCoord, dif_pos (And.intro hi1 hi2)]
  show next c (traj c π d t) (orderAt c π d t) (d t) ⟨i - 1, _⟩ = _
  simp only [next, outdatedAt, level]
  have : i - 1 + 2 = i + 1 := by omega
  rw [this]; rfl

theorem iter (c : Params) (π : Policy c) (d : DemandPath) (t n : ℕ)
    (hn : n ≤ c.m + c.L) : ∀ k : ℕ, k + 1 ≤ n →
    levelAt c π d (t + k) (n - k) = levelAt c π d t n -
      ∑ i ∈ Finset.Ico t (t + k), (d i : ℝ) - ∑ i ∈ Finset.Ico t (t + k), outdatedAt c π d i := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := step c π d (t + k) (n - (k + 1)) (by omega) (by omega)
    have e1 : n - (k + 1) + 1 = n - k := by omega
    rw [e1, h1] at h2
    rw [show t + (k + 1) = t + k + 1 by omega, h2, Finset.sum_Ico_succ_top (by omega),
      Finset.sum_Ico_succ_top (by omega)]
    ring

theorem stateCoord_zero (c : Params) (i : ℕ) : stateCoord c (0 : State c) i = 0 := by
  unfold stateCoord; split_ifs <;> rfl

theorem levelAt_state (c : Params) (π : Policy c) (d : DemandPath) (t i : ℕ)
    (hi : i ≠ c.m + c.L) : levelAt c π d t i = stateCoord c (traj c π d t) i := by
  simp only [levelAt, level, if_neg hi]

/-- Under `π_S` the inventory position after ordering is always `S`. -/
theorem bs_top (c : Params) (hm : 1 ≤ c.m) (S : ℝ≥0) (d : DemandPath) (t : ℕ) :
    levelAt c (baseStock c S) d t (c.m + c.L) = S := by
  have key : ∀ t, stateCoord c (traj c (baseStock c S) d t) (c.m + c.L - 1) ≤ S →
      levelAt c (baseStock c S) d t (c.m + c.L) = S := by
    intro t h
    have e1 : levelAt c (baseStock c S) d t (c.m + c.L) =
        stateCoord c (traj c (baseStock c S) d t) (c.m + c.L - 1) +
          max ((S : ℝ) - stateCoord c (traj c (baseStock c S) d t) (c.m + c.L - 1)) 0 := by
      unfold levelAt level; rw [if_pos rfl]; unfold orderUpTo; congr 1
    rw [e1]
    rcases le_total ((S : ℝ) - stateCoord c (traj c (baseStock c S) d t) (c.m + c.L - 1)) 0
      with h1 | h1
    · rw [max_eq_right h1]; linarith
    · rw [max_eq_left h1]; ring
  induction t with
  | zero => exact key 0 (by simp [traj, stateCoord_zero])
  | succ t ih =>
    apply key
    by_cases hML : 1 ≤ c.m + c.L - 1
    · rw [← levelAt_state c _ d _ _ (by omega), step c _ d t _ hML le_rfl,
        show c.m + c.L - 1 + 1 = c.m + c.L by omega, ih]
      have := outdated_nonneg c (baseStock c S) d t
      have : (0 : ℝ) ≤ d t := NNReal.coe_nonneg _
      linarith
    · have : c.m + c.L - 1 = 0 := by omega
      rw [this]; unfold stateCoord; rw [dif_neg (by omega)]; exact S.2

/-- crude two-sided bounds on all levels under `π_S` -/
theorem bs_bounds (c : Params) (hm : 1 ≤ c.m) (S : ℝ≥0) (d : DemandPath) (s : ℕ) :
    ∀ i, 1 ≤ i → i ≤ c.m + c.L →
      -(∑ j ∈ Finset.range s, (d j : ℝ)) - s * (S : ℝ) ≤ levelAt c (baseStock c S) d s i ∧
      levelAt c (baseStock c S) d s i ≤ S := by
  induction s with
  | zero =>
    intro i hi1 hi2
    by_cases h : i = c.m + c.L
    · subst h; rw [bs_top c hm]; simp
    · rw [levelAt_state c _ d _ _ h]; simp [traj, stateCoord_zero]
  | succ s ih =>
    intro i hi1 hi2
    by_cases h : i = c.m + c.L
    · subst h; rw [bs_top c hm]
      have : (0 : ℝ) ≤ ∑ j ∈ Finset.range (s + 1), (d j : ℝ) :=
        Finset.sum_nonneg fun j _ => NNReal.coe_nonneg _
      constructor <;> [nlinarith [S.2]; exact le_rfl]
    · rw [step c _ d s i hi1 (by omega)]
      obtain ⟨l1, u1⟩ := ih (i + 1) (by omega) (by omega)
      obtain ⟨l0, u0⟩ := ih 1 le_rfl (by omega)
      have ho0 := outdated_nonneg c (baseStock c S) d s
      have hoS : outdatedAt c (baseStock c S) d s ≤ S := by
        unfold outdatedAt; show max _ 0 ≤ _
        exact max_le (by have := NNReal.coe_nonneg (d s); unfold levelAt at u0; linarith) S.2
      have hd : (0 : ℝ) ≤ d s := NNReal.coe_nonneg _
      rw [Finset.sum_range_succ]; push_cast
      constructor <;> linarith

theorem shift_integral (P : DemandLaw) (f : ℝ → ℝ) (hf : Measurable f) (j k : ℕ) :
    ∫ d, f (∑ i ∈ Finset.Ico j (j + k), ((d i : ℝ≥0) : ℝ)) ∂demandPathLaw P =
      ∫ d, f (∑ i ∈ Finset.range k, ((d i : ℝ≥0) : ℝ)) ∂demandPathLaw P := by
  have hshm : Measurable (fun d : DemandPath => fun i => d (j + i)) := by fun_prop
  conv_rhs => rw [← shift_map P j]
  have hm2 : Measurable (fun d : DemandPath => f (∑ i ∈ Finset.range k, ((d i : ℝ≥0) : ℝ))) :=
    hf.comp (meas_sumR k)
  rw [integral_map hshm.aemeasurable hm2.aestronglyMeasurable]
  congr 1; ext d; rw [sum_Ico_shift]

theorem eh_shift (P : DemandLaw) (S : ℝ≥0) (j k : ℕ) :
    ∫ d, max ((S : ℝ) - ∑ i ∈ Finset.Ico j (j + (k + 1)), ((d i : ℝ≥0) : ℝ)) 0 ∂demandPathLaw P =
      expectedHolding (leadTimeLaw P k) S := by
  rw [eh_as, shift_integral P (fun x => max ((S : ℝ) - x) 0) (by fun_prop)]

theorem es_shift (P : DemandLaw) (S : ℝ≥0) (j k : ℕ) :
    ∫ d, max (∑ i ∈ Finset.Ico j (j + (k + 1)), ((d i : ℝ≥0) : ℝ) - S) 0 ∂demandPathLaw P =
      expectedShortfall (leadTimeLaw P k) S := by
  rw [es_as, shift_integral P (fun x => max (x - (S : ℝ)) 0) (by fun_prop)]

theorem meas_sumIco (j k : ℕ) :
    Measurable (fun d : DemandPath => ∑ i ∈ Finset.Ico j (j + k), ((d i : ℝ≥0) : ℝ)) :=
  Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).coe_nnreal_real

theorem int_eh_shift (P : DemandLaw) (S : ℝ≥0) (j k : ℕ) :
    Integrable (fun d : DemandPath =>
      max ((S : ℝ) - ∑ i ∈ Finset.Ico j (j + k), ((d i : ℝ≥0) : ℝ)) 0) (demandPathLaw P) := by
  refine Integrable.of_bound ((measurable_const.sub (meas_sumIco j k)).max
    measurable_const).aestronglyMeasurable (S : ℝ) (ae_of_all _ fun d => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  have : (0 : ℝ) ≤ ∑ i ∈ Finset.Ico j (j + k), ((d i : ℝ≥0) : ℝ) :=
    Finset.sum_nonneg fun i _ => NNReal.coe_nonneg _
  exact max_le (by linarith) S.2

theorem int_sumIco (P : DemandLaw) (j k : ℕ) :
    Integrable (fun d : DemandPath => ∑ i ∈ Finset.Ico j (j + k), ((d i : ℝ≥0) : ℝ))
      (demandPathLaw P) :=
  integrable_finsetSum _ fun i _ => coord_integrable P i

theorem int_es_shift (P : DemandLaw) (S : ℝ≥0) (j k : ℕ) :
    Integrable (fun d : DemandPath =>
      max (∑ i ∈ Finset.Ico j (j + k), ((d i : ℝ≥0) : ℝ) - S) 0) (demandPathLaw P) := by
  refine (int_sumIco P j k).mono' (((meas_sumIco j k).sub measurable_const).max
    measurable_const).aestronglyMeasurable (ae_of_all _ fun d => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith [S.2]) (Finset.sum_nonneg fun i _ => NNReal.coe_nonneg _)

/-- outdating bound (EC.27), pathwise -/
theorem o_bound (c : Params) (hm : 1 ≤ c.m) (S : ℝ≥0) (d : DemandPath) (t : ℕ) :
    outdatedAt c (baseStock c S) d (t + (c.m + c.L - 1)) ≤
      max ((S : ℝ) - ∑ i ∈ Finset.Ico t (t + (c.m + c.L - 1 + 1)), (d i : ℝ)) 0 := by
  have h := iter c (baseStock c S) d t (c.m + c.L) le_rfl (c.m + c.L - 1) (by omega)
  rw [show c.m + c.L - (c.m + c.L - 1) = 1 by omega, bs_top c hm] at h
  unfold outdatedAt; show max _ 0 ≤ _
  apply max_le_max _ le_rfl
  change levelAt c (baseStock c S) d _ 1 - _ ≤ _
  rw [h, show t + (c.m + c.L - 1 + 1) = t + (c.m + c.L - 1) + 1 by ring,
    Finset.sum_Ico_succ_top (by omega)]
  have : 0 ≤ ∑ i ∈ Finset.Ico t (t + (c.m + c.L - 1)), outdatedAt c (baseStock c S) d i :=
    Finset.sum_nonneg fun i _ => outdated_nonneg _ _ _ _
  linarith

/-- (EC.26)-(EC.28) pathwise: the period cost at `s = t + L` with `t ≥ m + L - 1`. -/
theorem rc_bound (c : Params) (hc : c.Standing) (S : ℝ≥0) (d : DemandPath) (t : ℕ)
    (ht : c.m + c.L - 1 ≤ t) :
    rc c (baseStock c S) d (t + c.L) ≤
      c.h * max ((S : ℝ) - ∑ i ∈ Finset.Ico t (t + (c.L + 1)), (d i : ℝ)) 0 +
      c.b * max (∑ i ∈ Finset.Ico t (t + (c.L + 1)), (d i : ℝ) - S) 0 +
      c.b * ∑ j ∈ Finset.range c.L, max ((S : ℝ) - ∑ i ∈ Finset.Ico (t + j - (c.m + c.L - 1))
          (t + j - (c.m + c.L - 1) + (c.m + c.L - 1 + 1)), (d i : ℝ)) 0 +
      c.θ * max ((S : ℝ) - ∑ i ∈ Finset.Ico (t + c.L - (c.m + c.L - 1))
          (t + c.L - (c.m + c.L - 1) + (c.m + c.L - 1 + 1)), (d i : ℝ)) 0 := by
  obtain ⟨hm1, hh, hb, hθ⟩ := hc
  have hL0 : (0 : ℝ) ≤ c.L := Nat.cast_nonneg _
  have hθ0 : 0 ≤ c.θ := le_trans (by positivity) hθ
  set π := baseStock c S
  have e29 := iter c π d t (c.m + c.L) le_rfl c.L (by omega)
  rw [show c.m + c.L - c.L = c.m by omega, bs_top c hm1] at e29
  set A := ∑ i ∈ Finset.Ico t (t + c.L), (d i : ℝ)
  set O := ∑ i ∈ Finset.Ico t (t + c.L), outdatedAt c π d i
  have hO : 0 ≤ O := Finset.sum_nonneg fun i _ => outdated_nonneg _ _ _ _
  have hA1 : ∑ i ∈ Finset.Ico t (t + (c.L + 1)), (d i : ℝ) = A + d (t + c.L) := by
    rw [show t + (c.L + 1) = t + c.L + 1 by ring, Finset.sum_Ico_succ_top (by omega)]
  -- each outdating in the window
  have hOb : O ≤ ∑ j ∈ Finset.range c.L, max ((S : ℝ) - ∑ i ∈ Finset.Ico (t + j - (c.m + c.L - 1))
          (t + j - (c.m + c.L - 1) + (c.m + c.L - 1 + 1)), (d i : ℝ)) 0 := by
    simp only [O]
    rw [Finset.sum_Ico_eq_sum_range, show t + c.L - t = c.L by omega]
    apply Finset.sum_le_sum; intro j _
    have := o_bound c hm1 S d (t + j - (c.m + c.L - 1))
    rwa [show t + j - (c.m + c.L - 1) + (c.m + c.L - 1) = t + j by omega] at this
  have hos := o_bound c hm1 S d (t + c.L - (c.m + c.L - 1))
  rw [show t + c.L - (c.m + c.L - 1) + (c.m + c.L - 1) = t + c.L by omega] at hos
  unfold rc
  rw [e29, hA1]
  set y := (S : ℝ)
  have k1 : max (y - A - O - d (t + c.L)) 0 ≤ max (y - (A + d (t + c.L))) 0 :=
    max_le_max (by linarith) le_rfl
  have k2 : max ((d (t + c.L) : ℝ) - (y - A - O)) 0 ≤ max (A + d (t + c.L) - y) 0 + O := by
    rcases le_total ((d (t + c.L) : ℝ) - (y - A - O)) 0 with h | h
    · rw [max_eq_right h]; linarith [le_max_right (A + d (t + c.L) - y) 0]
    · rw [max_eq_left h]; linarith [le_max_left (A + d (t + c.L) - y) 0]
  nlinarith [mul_le_mul_of_nonneg_left k1 hh.le, mul_le_mul_of_nonneg_left k2 hb.le,
    mul_le_mul_of_nonneg_left hOb hb.le, mul_le_mul_of_nonneg_left hos hθ0]

end PB7B

namespace PB7B
open PerishBaseStock.Backlog LostSalesOrderUpTo.Asymptotic CappedBaseStock PB7H PB7P PB7E

theorem early_finite (P : DemandLaw) (c : Params) (hc : c.Standing) (S : ℝ≥0) (s : ℕ) :
    ∫⁻ d, costAt c (baseStock c S) d s ∂demandPathLaw P ≠ ⊤ := by
  obtain ⟨hm1, hh, hb, hθ⟩ := hc
  have hL0 : (0 : ℝ) ≤ c.L := Nat.cast_nonneg _
  have hθ0 : 0 ≤ c.θ := le_trans (by positivity) hθ
  set g : DemandPath → ℝ := fun d => (c.h + c.θ) * S +
    c.b * ((d s : ℝ) + ∑ j ∈ Finset.range s, (d j : ℝ) + s * S)
  have hg : Integrable g (demandPathLaw P) := by
    refine (integrable_const _).add (((coord_integrable P s).add
      (integrable_finsetSum _ fun j _ => coord_integrable P j)).add (integrable_const _)
        |>.const_mul _)
  refine ne_top_of_le_ne_top (hg.lintegral_lt_top).ne (lintegral_mono fun d => ?_)
  rw [costAt_eq]
  apply ENNReal.ofReal_le_ofReal
  obtain ⟨lo, up⟩ := bs_bounds c hm1 S d s c.m hm1 (by omega)
  obtain ⟨-, up1⟩ := bs_bounds c hm1 S d s 1 le_rfl (by omega)
  have ho0 := outdated_nonneg c (baseStock c S) d s
  have hoS : outdatedAt c (baseStock c S) d s ≤ S := by
    unfold outdatedAt; show max _ 0 ≤ _
    exact max_le (by have := NNReal.coe_nonneg (d s); unfold levelAt at up1; linarith) S.2
  have hd : (0 : ℝ) ≤ d s := NNReal.coe_nonneg _
  have hsum : (0 : ℝ) ≤ ∑ j ∈ Finset.range s, (d j : ℝ) :=
    Finset.sum_nonneg fun j _ => NNReal.coe_nonneg _
  have hS0 : (0 : ℝ) ≤ S := S.2
  have k1 : max (levelAt c (baseStock c S) d s c.m - d s) 0 ≤ S := max_le (by linarith) hS0
  have k2 : max ((d s : ℝ) - levelAt c (baseStock c S) d s c.m) 0 ≤
      (d s : ℝ) + ∑ j ∈ Finset.range s, (d j : ℝ) + s * S :=
    max_le (by linarith) (by positivity)
  unfold rc
  simp only [g]
  nlinarith [mul_le_mul_of_nonneg_left k1 hh.le, mul_le_mul_of_nonneg_left k2 hb.le,
    mul_le_mul_of_nonneg_left hoS hθ0]

theorem late_bound (P : DemandLaw) (c : Params) (hc : c.Standing) (S : ℝ≥0) (t : ℕ)
    (ht : c.m + c.L - 1 ≤ t) :
    ∫⁻ d, costAt c (baseStock c S) d (t + c.L) ∂demandPathLaw P ≤ ENNReal.ofReal
      (c.h * expectedHolding (leadTimeLaw P c.L) S +
        c.b * expectedShortfall (leadTimeLaw P c.L) S +
        (c.θ + c.b * c.L) * expectedHolding (leadTimeLaw P (c.m + c.L - 1)) S) := by
  set k := c.m + c.L - 1
  set f1 : DemandPath → ℝ := fun d => max ((S : ℝ) - ∑ i ∈ Finset.Ico t (t + (c.L + 1)), (d i : ℝ)) 0
  set f2 : DemandPath → ℝ := fun d => max (∑ i ∈ Finset.Ico t (t + (c.L + 1)), (d i : ℝ) - S) 0
  set f3 : ℕ → DemandPath → ℝ := fun j d => max ((S : ℝ) - ∑ i ∈ Finset.Ico (t + j - k)
          (t + j - k + (k + 1)), (d i : ℝ)) 0
  set f4 : DemandPath → ℝ := fun d => max ((S : ℝ) - ∑ i ∈ Finset.Ico (t + c.L - k)
          (t + c.L - k + (k + 1)), (d i : ℝ)) 0
  have i1 : Integrable f1 (demandPathLaw P) := int_eh_shift P S _ _
  have i2 : Integrable f2 (demandPathLaw P) := int_es_shift P S _ _
  have i3 : ∀ j, Integrable (f3 j) (demandPathLaw P) := fun j => int_eh_shift P S _ _
  have i4 : Integrable f4 (demandPathLaw P) := int_eh_shift P S _ _
  have hA : Integrable (fun d => c.h * f1 d + c.b * f2 d) (demandPathLaw P) :=
    (i1.const_mul _).add (i2.const_mul _)
  have hB : Integrable (fun d => c.b * ∑ j ∈ Finset.range c.L, f3 j d) (demandPathLaw P) :=
    (integrable_finsetSum _ fun j _ => i3 j).const_mul _
  have hC : Integrable (fun d => c.θ * f4 d) (demandPathLaw P) := i4.const_mul _
  set Bnd : DemandPath → ℝ := fun d => (c.h * f1 d + c.b * f2 d) +
    c.b * ∑ j ∈ Finset.range c.L, f3 j d + c.θ * f4 d
  have hBi : Integrable Bnd (demandPathLaw P) := (hA.add hB).add hC
  have hpt : ∀ d, rc c (baseStock c S) d (t + c.L) ≤ Bnd d := fun d => rc_bound c hc S d t ht
  have hBnn : 0 ≤ᵐ[demandPathLaw P] Bnd := ae_of_all _ fun d =>
    le_trans (rc_nonneg c hc _ d _) (hpt d)
  have hint : ∫ d, Bnd d ∂demandPathLaw P =
      c.h * expectedHolding (leadTimeLaw P c.L) S +
        c.b * expectedShortfall (leadTimeLaw P c.L) S +
        (c.θ + c.b * c.L) * expectedHolding (leadTimeLaw P (c.m + c.L - 1)) S := by
    have hAB : Integrable (fun d => c.h * f1 d + c.b * f2 d +
        c.b * ∑ j ∈ Finset.range c.L, f3 j d) (demandPathLaw P) := hA.add hB
    simp only [Bnd]
    rw [integral_add hAB hC, integral_add hA hB, integral_add (i1.const_mul _)
      (i2.const_mul _), integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_finset_sum _ fun j _ => i3 j]
    simp only [f1, f2, f3, f4]
    rw [eh_shift, es_shift, eh_shift]
    simp only [eh_shift, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  calc ∫⁻ d, costAt c (baseStock c S) d (t + c.L) ∂demandPathLaw P
      ≤ ∫⁻ d, ENNReal.ofReal (Bnd d) ∂demandPathLaw P :=
        lintegral_mono fun d => by rw [costAt_eq]; exact ENNReal.ofReal_le_ofReal (hpt d)
    _ = _ := by rw [← ofReal_integral_eq_lintegral_ofReal hBi hBnn, hint]

theorem upper (P : DemandLaw) (c : Params) (hc : c.Standing) (S : ℝ≥0) :
    bsCost P c S ≤ ENNReal.ofReal
      (c.h * expectedHolding (leadTimeLaw P c.L) S +
        c.b * expectedShortfall (leadTimeLaw P c.L) S +
        (c.θ + c.b * c.L) * expectedHolding (leadTimeLaw P (c.m + c.L - 1)) S) := by
  set U := ENNReal.ofReal
      (c.h * expectedHolding (leadTimeLaw P c.L) S +
        c.b * expectedShortfall (leadTimeLaw P c.L) S +
        (c.θ + c.b * c.L) * expectedHolding (leadTimeLaw P (c.m + c.L - 1)) S)
  set a : ℕ → ℝ≥0∞ := fun s => ∫⁻ d, costAt c (baseStock c S) d s ∂demandPathLaw P
  set t0 := c.m + c.L - 1 + c.L
  set A0 := ∑ s ∈ Finset.range t0, a s
  have hA0 : A0 ≠ ⊤ := ENNReal.sum_ne_top.2 fun s _ => early_finite P c hc S s
  have hterm : ∀ s, a s ≤ (if s < t0 then a s else 0) + U := by
    intro s
    split_ifs with h
    · exact le_add_right le_rfl
    · rw [zero_add]
      have := late_bound P c hc S (s - c.L) (by omega)
      rwa [show s - c.L + c.L = s by omega] at this
  have hsum : ∀ N, ∑ s ∈ Finset.range N, a s ≤ A0 + N * U := by
    intro N
    calc ∑ s ∈ Finset.range N, a s ≤ ∑ s ∈ Finset.range N, ((if s < t0 then a s else 0) + U) :=
          Finset.sum_le_sum fun s _ => hterm s
      _ = ∑ s ∈ Finset.range N, (if s < t0 then a s else 0) + N * U := by
          rw [Finset.sum_add_distrib]; simp
      _ ≤ A0 + N * U := by
          gcongr
          rw [← Finset.sum_filter]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro s hs; simp only [Finset.mem_filter, Finset.mem_range] at hs ⊢; exact hs.2
          · intro _ _ _; exact bot_le
  have hlim : Tendsto (fun N : ℕ => (N : ℝ≥0∞)⁻¹ * (A0 + N * U)) atTop (𝓝 U) := by
    have h1 : Tendsto (fun N : ℕ => (N : ℝ≥0∞)⁻¹ * A0) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hA0)
    have h2 : (fun N : ℕ => (N : ℝ≥0∞)⁻¹ * (A0 + N * U)) =ᶠ[atTop]
        fun N => (N : ℝ≥0∞)⁻¹ * A0 + U := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [mul_add, ← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast (show N ≠ 0 by omega))
        (ENNReal.natCast_ne_top N), one_mul]
    simpa using (h1.add tendsto_const_nhds).congr' h2.symm
  unfold bsCost PerishBaseStock.Backlog.policyCost
  calc _ ≤ limsup (fun N : ℕ => (N : ℝ≥0∞)⁻¹ * (A0 + N * U)) atTop :=
        limsup_le_limsup (Eventually.of_forall fun N => mul_le_mul_right (hsum N) _)
    _ = U := hlim.limsup_eq

end PB7B

open PerishBaseStock.Backlog LostSalesOrderUpTo.Asymptotic in
theorem solution (P : CappedBaseStock.DemandLaw) (c : Params) (hc : c.Standing) (S : ℝ≥0) :
    bsCost P c S ≤ ENNReal.ofReal
        (c.h * expectedHolding (leadTimeLaw P c.L) S +
          c.b * expectedShortfall (leadTimeLaw P c.L) S +
          (c.θ + c.b * c.L) * expectedHolding (leadTimeLaw P (c.m + c.L - 1)) S) ∧
      ENNReal.ofReal (heuristicCost P c S) ≤ bsCost P c S := by
  refine ⟨PB7B.upper P c hc S, ?_⟩
  refine PB7E.engine P c hc (baseStock c S) _ fun t => ?_
  simp only [PB7B.bs_top c hc.1 S]
  exact PB7E.psi_expect P c hc S t
