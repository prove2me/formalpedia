-- Prove2me | solution 1 for PerishBaseStock.Backlog.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T19:47:00.491724+00:00
-- url     : https://prove2.me/submissions/576d4bba-88b2-49d1-88eb-9a5098290363

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

namespace PB7Q
open PerishBaseStock.Backlog LostSalesOrderUpTo.Asymptotic CappedBaseStock PB7H PB7P PB7E
open ProbabilityTheory

theorem traj_congr (c : Params) (π : Policy c) (d d' : DemandPath) (t : ℕ)
    (h : ∀ i < t, d i = d' i) : traj c π d t = traj c π d' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hs := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    simp only [traj, hs, h t (Nat.lt_succ_self t)]

theorem levelAt_congr (c : Params) (π : Policy c) (d d' : DemandPath) (t i : ℕ)
    (h : ∀ j < t, d j = d' j) : levelAt c π d t i = levelAt c π d' t i := by
  unfold levelAt orderAt; rw [traj_congr c π d d' t h]

/-- extend a history on `range t` by zeros -/
def ext (t : ℕ) (v : (Finset.range t) → ℝ≥0) : DemandPath :=
  fun i => if h : i ∈ Finset.range t then v ⟨i, h⟩ else 0

theorem meas_ext (t : ℕ) : Measurable (ext t) := by
  refine measurable_pi_lambda _ fun i => ?_
  unfold ext
  split_ifs with h
  · exact measurable_pi_apply _
  · exact measurable_const

/-- the two lead-time sums read off the future block `Ico t (t+m+L)` -/
def futSums (c : Params) (t : ℕ) (v : (Finset.Ico t (t + c.m + c.L)) → ℝ≥0) : ℝ × ℝ :=
  (∑ i : (Finset.Ico t (t + c.m + c.L)), if i.1 < t + c.L + 1 then ((v i : ℝ≥0) : ℝ) else 0,
   ∑ i : (Finset.Ico t (t + c.m + c.L)), ((v i : ℝ≥0) : ℝ))

theorem meas_futSums (c : Params) (t : ℕ) : Measurable (futSums c t) := by
  unfold futSums
  refine Measurable.prodMk (Finset.measurable_sum _ fun i _ => ?_)
    (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).coe_nnreal_real)
  split_ifs
  · exact (measurable_pi_apply i).coe_nnreal_real
  · exact measurable_const

theorem futSums_eq (c : Params) (hm : 1 ≤ c.m) (t : ℕ) (d : DemandPath) :
    futSums c t (fun i => d i) = (X1 c d t, Xm c d t) := by
  unfold futSums X1 Xm
  congr 1
  · rw [Finset.sum_coe_sort (Finset.Ico t (t + c.m + c.L))
      (fun i => if i < t + c.L + 1 then ((d i : ℝ≥0) : ℝ) else 0), ← Finset.sum_filter]
    congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_Ico]; omega
  · exact Finset.sum_coe_sort (Finset.Ico t (t + c.m + c.L)) (fun i => ((d i : ℝ≥0) : ℝ))

theorem X1_nonneg (c : Params) (d : DemandPath) (t : ℕ) : 0 ≤ X1 c d t :=
  Finset.sum_nonneg fun i _ => NNReal.coe_nonneg _

theorem Xm_nonneg (c : Params) (d : DemandPath) (t : ℕ) : 0 ≤ Xm c d t :=
  Finset.sum_nonneg fun i _ => NNReal.coe_nonneg _

/-- For any admissible policy, each period's (EC.33) integrand has expectation `≥ C̃^L(S̃^L)`. -/
theorem per_period (P : DemandLaw) (c : Params) (hc : c.Standing) (π : Policy c) (S : ℝ≥0)
    (hS : IsHeuristicLevel P c S) (t : ℕ) :
    ENNReal.ofReal (heuristicCost P c S) ≤ ∫⁻ d, ENNReal.ofReal
      (psi c (levelAt c π d t (c.m + c.L)) (X1 c d t) (Xm c d t)) ∂demandPathLaw P := by
  set ν := demandPathLaw P
  set Y : DemandPath → ℝ := fun d => levelAt c π d t (c.m + c.L)
  set V : DemandPath → ℝ × ℝ := fun d => (X1 c d t, Xm c d t)
  have hYm : Measurable Y := meas_levelAt c π t _
  have hVm : Measurable V := (meas_X1 c t).prodMk (meas_Xm c t)
  -- independence of the past level and the future demand sums
  have hind0 : iIndepFun (fun i (d : DemandPath) => d i) ν := by
    unfold ν demandPathLaw
    exact iIndepFun_infinitePi (X := fun _ (x : ℝ≥0) => x) (fun _ => measurable_id)
  have hdisj : Disjoint (Finset.range t) (Finset.Ico t (t + c.m + c.L)) := by
    rw [Finset.disjoint_left]; intro i h1 h2
    simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
  have hind1 := hind0.indepFun_finset _ _ hdisj (fun i => measurable_pi_apply i)
  set g : ((Finset.range t) → ℝ≥0) → ℝ := fun v => levelAt c π (ext t v) t (c.m + c.L)
  have hgm : Measurable g := (meas_levelAt c π t _).comp (meas_ext t)
  have hind2 := hind1.comp hgm (meas_futSums c t)
  have hY : (g ∘ fun d (i : Finset.range t) => d i) = Y := by
    ext d
    simp only [Function.comp, g, Y]
    apply levelAt_congr
    intro j hj
    simp [ext, Finset.mem_range.2 hj]
  have hV : (futSums c t ∘ fun d (i : Finset.Ico t (t + c.m + c.L)) => d i) = V := by
    ext d <;> simp only [Function.comp, V, futSums_eq c hc.1 t d]
  rw [hY, hV] at hind2
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hYm.aemeasurable hVm.aemeasurable).1 hind2
  set F : ℝ × (ℝ × ℝ) → ℝ≥0∞ := fun p => ENNReal.ofReal (psi c p.1 p.2.1 p.2.2)
  have hFm : Measurable F := (meas_psi c).ennreal_ofReal
  have hrw : ∫⁻ d, ENNReal.ofReal (psi c (levelAt c π d t (c.m + c.L)) (X1 c d t) (Xm c d t)) ∂ν
      = ∫⁻ p, F p ∂(ν.map Y).prod (ν.map V) := by
    rw [← hprod, lintegral_map hFm (hYm.prodMk hVm)]
  rw [hrw, lintegral_prod _ hFm.aemeasurable]
  haveI : IsProbabilityMeasure (ν.map Y) := Measure.isProbabilityMeasure_map hYm.aemeasurable
  calc ENNReal.ofReal (heuristicCost P c S)
      = ∫⁻ _y, ENNReal.ofReal (heuristicCost P c S) ∂(ν.map Y) := by simp
    _ ≤ _ := lintegral_mono fun y => ?_
  -- inner bound
  rw [lintegral_map (f := fun v => F (y, v)) (hFm.comp (measurable_const.prodMk measurable_id)) hVm]
  simp only [F, V]
  calc ENNReal.ofReal (heuristicCost P c S)
      ≤ ENNReal.ofReal (heuristicCost P c (Real.toNNReal y)) :=
        ENNReal.ofReal_le_ofReal (hS _)
    _ ≤ ∫⁻ d, ENNReal.ofReal (psi c (Real.toNNReal y) (X1 c d t) (Xm c d t)) ∂ν :=
        psi_expect P c hc _ t
    _ ≤ _ := lintegral_mono fun d => ENNReal.ofReal_le_ofReal (by
        rw [Real.coe_toNNReal']
        exact psi_pos_part c y _ _ (X1_nonneg c d t) (Xm_nonneg c d t) hc)

end PB7Q

open PerishBaseStock.Backlog in
theorem solution (P : CappedBaseStock.DemandLaw) (c : Params) (hc : c.Standing)
    (hL : 1 ≤ c.L) (S : ℝ≥0) (hS : IsHeuristicLevel P c S) :
    ENNReal.ofReal (heuristicCost P c S) ≤ OPT P c :=
  le_iInf fun π => PB7E.engine P c hc π _ (PB7Q.per_period P c hc π S hS)
