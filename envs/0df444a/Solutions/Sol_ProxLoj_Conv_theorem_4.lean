-- Prove2me | solution 1 for ProxLoj.Conv.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-27T08:43:38.493978+00:00
-- url     : https://prove2.me/submissions/017ef5f8-4372-481a-993f-fc93f2324fe0

import Definitions.Def_ProxLoj_Conv_Setting
import Mathlib


open Filter Topology NonconvexSplitting.Shared NonsmoothLojasiewicz.Continuous
open scoped InnerProductSpace
namespace ProxLoj.Conv.PLFresh

variable {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → EReal}
  {lam : ℕ → ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)}

theorem prox_finite_succ (hp : IsProper f) (hx : IsProxRun f lam x) (k : ℕ) :
    f (x (k + 1)) ≠ ⊤ := by
  obtain ⟨u, hu⟩ := hp.2
  have hh := hx k u
  have hb := EReal.add_lt_top hu (EReal.coe_ne_top (‖u - x k‖ ^ 2 / (2 * lam k)))
  intro he
  rw [he, EReal.top_add_coe] at hh
  exact (not_lt_of_ge hh) hb

theorem prox_real_comparison (hp : IsProper f) (hx : IsProxRun f lam x)
    (k : ℕ) (u : EuclideanSpace ℝ (Fin n)) (hu : f u ≠ ⊤) :
    (f (x (k + 1))).toReal + ‖x (k + 1) - x k‖ ^ 2 / (2 * lam k) ≤
      (f u).toReal + ‖u - x k‖ ^ 2 / (2 * lam k) := by
  have hh := hx k u
  rw [← EReal.coe_toReal (prox_finite_succ hp hx k) (hp.1 _),
    ← EReal.coe_toReal hu (hp.1 u), ← EReal.coe_add, ← EReal.coe_add,
    EReal.coe_le_coe_iff] at hh
  exact hh

theorem prox_tail_descent (hp : IsProper f) (hx : IsProxRun f lam x) (k : ℕ) :
    (f (x (k + 2))).toReal + ‖x (k + 2) - x (k + 1)‖ ^ 2 /
      (2 * lam (k + 1)) ≤ (f (x (k + 1))).toReal := by
  simpa only [sub_self, norm_zero, sq, zero_mul, zero_div, add_zero] using
    prox_real_comparison hp hx (k + 1) (x (k + 1)) (prox_finite_succ hp hx k)

theorem prox_tail_lower (hH1 : H1 f) (hx : IsProxRun f lam x) (hp : IsProper f) :
    ∃ m : ℝ, ∀ k, m ≤ (f (x (k + 1))).toReal := by
  obtain ⟨m, hm⟩ := hH1
  refine ⟨m, fun k => ?_⟩
  have hh := EReal.toReal_le_toReal (hm (x (k + 1))) (EReal.coe_ne_bot m)
    (prox_finite_succ hp hx k)
  simpa using hh

theorem step_pos {lo hi : ℝ} (hs : StepBounds lam lo hi) (k : ℕ) : 0 < lam k :=
  hs.1.trans (hs.2.2 k).1

end ProxLoj.Conv.PLFresh


open Filter Topology NonconvexSplitting.Shared NonsmoothLojasiewicz.Continuous
namespace ProxLoj.Conv.PLFresh

variable {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → EReal}
  {lam : ℕ → ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)} {lo hi : ℝ}

theorem energy_antitone (hp : IsProper f) (hx : IsProxRun f lam x)
    (hs : StepBounds lam lo hi) : Antitone (fun k => (f (x (k + 1))).toReal) := by
  apply antitone_nat_of_succ_le
  intro k
  have h := prox_tail_descent hp hx k
  have hz := div_nonneg (sq_nonneg ‖x (k + 2) - x (k + 1)‖)
    (le_of_lt (mul_pos (by norm_num : (0 : ℝ) < 2) (step_pos hs (k + 1))))
  linarith

theorem exists_energy_limit (hp : IsProper f) (hx : IsProxRun f lam x)
    (hs : StepBounds lam lo hi) (hb : H1 f) :
    ∃ l : ℝ, Tendsto (fun k => (f (x (k + 1))).toReal) atTop (𝓝 l) ∧
      ∀ k, l ≤ (f (x (k + 1))).toReal := by
  obtain ⟨m, hm⟩ := prox_tail_lower hb hx hp
  have hbd : BddBelow (Set.range (fun k => (f (x (k + 1))).toReal)) :=
    ⟨m, by rintro _ ⟨k, rfl⟩; exact hm k⟩
  have ha := energy_antitone hp hx hs
  have ht := tendsto_atTop_ciInf ha hbd
  exact ⟨_, ht, ha.le_of_tendsto ht⟩

theorem step_square_bound (hp : IsProper f) (hx : IsProxRun f lam x)
    (hs : StepBounds lam lo hi) (k : ℕ) :
    ‖x (k + 2) - x (k + 1)‖ ^ 2 ≤
      (2 * hi) * ((f (x (k + 1))).toReal - (f (x (k + 2))).toReal) := by
  have h := prox_tail_descent hp hx k
  have hd : 0 < 2 * lam (k + 1) := mul_pos (by norm_num) (step_pos hs _)
  have hq : ‖x (k + 2) - x (k + 1)‖ ^ 2 / (2 * lam (k + 1)) ≤
      (f (x (k + 1))).toReal - (f (x (k + 2))).toReal := by linarith
  have hm := (div_le_iff₀ hd).mp hq
  have he := energy_antitone hp hx hs (Nat.le_succ k)
  have hu := (hs.2.2 (k + 1)).2
  nlinarith

theorem tail_step_tendsto_zero (hp : IsProper f) (hx : IsProxRun f lam x)
    (hs : StepBounds lam lo hi) {l : ℝ}
    (hl : Tendsto (fun k => (f (x (k + 1))).toReal) atTop (𝓝 l)) :
    Tendsto (fun k => ‖x (k + 2) - x (k + 1)‖) atTop (𝓝 0) := by
  have hnext : Tendsto (fun k => (f (x (k + 2))).toReal) atTop (𝓝 l) :=
    hl.comp (tendsto_add_atTop_nat 1)
  have hb : Tendsto (fun k => (2 * hi) *
      ((f (x (k + 1))).toReal - (f (x (k + 2))).toReal)) atTop (𝓝 0) := by
    simpa using (hl.sub hnext).const_mul (2 * hi)
  have hsq : Tendsto (fun k => ‖x (k + 2) - x (k + 1)‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun k => sq_nonneg _) (step_square_bound hp hx hs) hb
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using ht

end ProxLoj.Conv.PLFresh


open Filter Topology NonconvexSplitting.Shared NonsmoothLojasiewicz.Continuous
open scoped InnerProductSpace
namespace ProxLoj.Conv.PLFresh

variable {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → EReal}
  {lam : ℕ → ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)}

noncomputable def proxVector (lam : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ) :=
  (lam k)⁻¹ • (x k - x (k + 1))

theorem prox_quad_identity (k : ℕ) (hl : lam k ≠ 0) (u : EuclideanSpace ℝ (Fin n)) :
    ‖u - x k‖ ^ 2 = ‖u - x (k + 1)‖ ^ 2 + ‖x (k + 1) - x k‖ ^ 2 -
      2 * lam k * ⟪proxVector lam x k, u - x (k + 1)⟫_ℝ := by
  have he : u - x k = (u - x (k + 1)) + (x (k + 1) - x k) := by abel
  rw [he, norm_add_sq_real]
  have hn : x k - x (k + 1) = -(x (k + 1) - x k) := by abel
  simp only [proxVector, hn, inner_smul_left, inner_neg_left, conj_trivial]
  rw [real_inner_comm (x (k + 1) - x k) (u - x (k + 1))]
  field_simp
  ring

theorem prox_regular (hp : IsProper f) (hx : IsProxRun f lam x)
    (k : ℕ) (hl : 0 < lam k) : IsRegularSubgrad f (x (k + 1)) (proxVector lam x k) := by
  refine ⟨prox_finite_succ hp hx k, fun ε hε => ?_⟩
  have hb := Metric.ball_mem_nhds (x (k + 1)) (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hl) hε)
  filter_upwards [hb] with u hu
  by_cases huf : f u = ⊤
  · rw [huf]
    exact le_top
  have hc := prox_real_comparison hp hx k u huf
  have hq := prox_quad_identity (x := x) k (ne_of_gt hl) u
  have hu' : ‖u - x (k + 1)‖ < 2 * lam k * ε := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hu
  have hn := norm_nonneg (u - x (k + 1))
  have hsmall : ‖u - x (k + 1)‖ ^ 2 ≤ 2 * lam k * ε * ‖u - x (k + 1)‖ := by
    nlinarith
  have hc' := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hl)).mp
    (show ‖x (k + 1) - x k‖ ^ 2 / (2 * lam k) ≤
      (f u).toReal - (f (x (k + 1))).toReal + ‖u - x k‖ ^ 2 / (2 * lam k) by linarith)
  have hden : 2 * lam k ≠ 0 := ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2) hl)
  have hcancel : (‖u - x k‖ ^ 2 / (2 * lam k)) * (2 * lam k) = ‖u - x k‖ ^ 2 :=
    div_mul_cancel₀ _ hden
  have hreal : (f (x (k + 1))).toReal +
      (⟪proxVector lam x k, u - x (k + 1)⟫_ℝ - ε * ‖u - x (k + 1)‖) ≤ (f u).toReal := by
    nlinarith
  rw [← EReal.coe_toReal (prox_finite_succ hp hx k) (hp.1 _),
    ← EReal.coe_toReal huf (hp.1 u), ← EReal.coe_add, EReal.coe_le_coe_iff]
  exact hreal

theorem regular_mem_limiting {y v : EuclideanSpace ℝ (Fin n)} (h : IsRegularSubgrad f y v) :
    v ∈ LimitingSubdiff f y :=
  ⟨h.1, fun _ => y, fun _ => v, tendsto_const_nhds, tendsto_const_nhds,
    tendsto_const_nhds, fun _ => h⟩

theorem prox_limiting (hp : IsProper f) (hx : IsProxRun f lam x)
    (k : ℕ) (hl : 0 < lam k) : proxVector lam x k ∈ LimitingSubdiff f (x (k + 1)) :=
  regular_mem_limiting (prox_regular hp hx k hl)

end ProxLoj.Conv.PLFresh


open Filter Topology NonconvexSplitting.Shared NonsmoothLojasiewicz.Continuous
open scoped InnerProductSpace
namespace ProxLoj.Conv.PLFresh

variable {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → EReal}
  {lam : ℕ → ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)} {lo hi l : ℝ}

theorem prox_vector_tail_zero (hp : IsProper f) (hx : IsProxRun f lam x)
    (hs : StepBounds lam lo hi)
    (hl : Tendsto (fun k => (f (x (k + 1))).toReal) atTop (𝓝 l)) :
    Tendsto (fun k => proxVector lam x (k + 1)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hb : Tendsto (fun k => lo⁻¹ * ‖x (k + 2) - x (k + 1)‖) atTop (𝓝 0) := by
    simpa using (tail_step_tendsto_zero hp hx hs hl).const_mul lo⁻¹
  apply squeeze_zero (fun k => norm_nonneg _) _ hb
  intro k
  have hk := step_pos hs (k + 1)
  have hinv : (lam (k + 1))⁻¹ ≤ lo⁻¹ := inv_anti₀ hs.1 (hs.2.2 (k + 1)).1.le
  simpa only [proxVector, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hk,
    norm_sub_rev] using mul_le_mul_of_nonneg_right hinv (norm_nonneg (x (k + 2) - x (k + 1)))

theorem exists_critical_cluster (hp : IsProper f) (hlsc : LowerSemicontinuous f)
    (hcont : H2 f) (hx : IsProxRun f lam x) (hs : StepBounds lam lo hi)
    (hbdd : Bornology.IsBounded (Set.range x))
    (hl : Tendsto (fun k => (f (x (k + 1))).toReal) atTop (𝓝 l)) :
    ∃ z : EuclideanSpace ℝ (Fin n), z ∈ crit f ∧ f z ≠ ⊤ ∧ (f z).toReal = l ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun k => x (φ k + 1)) atTop (𝓝 z) := by
  obtain ⟨z, _, φ, hφ, hconv⟩ := hbdd.isCompact_closure.tendsto_subseq
    (x := fun k => x (k + 2)) (fun k => subset_closure ⟨k + 2, rfl⟩)
  have hconv' : Tendsto (fun k => x (φ k + 2)) atTop (𝓝 z) := hconv
  have he := energy_antitone hp hx hs
  have hupper : ∀ k, f (x (k + 2)) ≤ f (x 1) := by
    intro k
    have hh := he (show 0 ≤ k + 1 by omega)
    rw [← EReal.coe_toReal (prox_finite_succ hp hx (k + 1)) (hp.1 _),
      ← EReal.coe_toReal (prox_finite_succ hp hx 0) (hp.1 _), EReal.coe_le_coe_iff]
    exact hh
  have hzupper : f z ≤ f (x 1) :=
    (hlsc.isClosed_preimage (f (x 1))).mem_of_tendsto hconv'
      (Filter.Eventually.of_forall (fun k => hupper (φ k)))
  have hzf : f z ≠ ⊤ := ne_top_of_le_ne_top (prox_finite_succ hp hx 0) hzupper
  have hvalues : Tendsto (fun k => f (x (φ k + 2))) atTop (𝓝 (f z)) :=
    Filter.Tendsto.comp (hcont z hzf)
      (tendsto_nhdsWithin_iff.mpr ⟨hconv',
        Filter.Eventually.of_forall (fun k => prox_finite_succ hp hx (φ k + 1))⟩)
  have hv := (prox_vector_tail_zero hp hx hs hl).comp hφ.tendsto_atTop
  have hzcrit : z ∈ crit f := by
    refine ⟨hzf, (fun k => x (φ k + 2)), (fun k => proxVector lam x (φ k + 1)),
      hconv', hvalues, hv, fun k => ?_⟩
    exact prox_regular hp hx (φ k + 1) (step_pos hs _)
  have heval : (f z).toReal = l := by
    have ht := (EReal.tendsto_toReal hzf (hp.1 z)).comp hvalues
    have hr : Tendsto (fun k => (f (x (φ k + 2))).toReal) atTop (𝓝 l) :=
      hl.comp ((tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop)
    exact tendsto_nhds_unique ht hr
  refine ⟨z, hzcrit, hzf, heval, (fun k => φ k + 1), ?_, hconv'⟩
  intro i j hij
  exact Nat.add_lt_add_right (hφ hij) 1

end ProxLoj.Conv.PLFresh


open Finset

namespace ProxLoj.Conv.PLFresh

theorem local_trapping {E : Type*} [PseudoMetricSpace E]
    (x : ℕ → E) (z : E) (a v : ℕ → ℝ) (R : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hv : ∀ n, 0 ≤ v n)
    (hstep : ∀ n, dist (x (n + 1)) (x n) ≤ a (n + 1))
    (hlocal : ∀ n, dist (x n) z < R →
      2 * a (n + 1) ≤ a n + v n - v (n + 1))
    (hstart : dist (x 0) z + a 0 + v 0 < R) :
    ∀ n, dist (x n) z < R ∧
      (∑ k ∈ range n, a (k + 1)) + a n + v n ≤ a 0 + v 0 := by
  have hpath : ∀ n, dist (x n) (x 0) ≤ ∑ k ∈ range n, a (k + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ]
      exact (dist_triangle (x (n + 1)) (x n) (x 0)).trans
        (by linarith [hstep n])
  intro n
  induction n with
  | zero =>
    constructor
    · linarith [ha 0, hv 0]
    · simp
  | succ n ih =>
    have hrec := hlocal n ih.1
    have hbudget : (∑ k ∈ range (n + 1), a (k + 1)) + a (n + 1) + v (n + 1) ≤
        a 0 + v 0 := by
      rw [sum_range_succ]
      linarith [ih.2]
    refine ⟨?_, hbudget⟩
    have ht := dist_triangle (x (n + 1)) (x 0) z
    have hp := hpath (n + 1)
    linarith [ha (n + 1), hv (n + 1)]

theorem local_trapping_summable {E : Type*} [PseudoMetricSpace E]
    (x : ℕ → E) (z : E) (a v : ℕ → ℝ) (R : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hv : ∀ n, 0 ≤ v n)
    (hstep : ∀ n, dist (x (n + 1)) (x n) ≤ a (n + 1))
    (hlocal : ∀ n, dist (x n) z < R →
      2 * a (n + 1) ≤ a n + v n - v (n + 1))
    (hstart : dist (x 0) z + a 0 + v 0 < R) :
    Summable (fun n => a (n + 1)) := by
  apply summable_of_sum_range_le (c := a 0 + v 0) (fun n => ha (n + 1))
  intro n
  have h := (local_trapping x z a v R ha hv hstep hlocal hstart n).2
  exact le_trans (by linarith [ha n, hv n]) h

end ProxLoj.Conv.PLFresh


open Filter Topology

namespace ProxLoj.Conv.PLFresh

theorem local_trapping_converges {E : Type*} [MetricSpace E] [CompleteSpace E]
    (x : ℕ → E) (z : E) (a v : ℕ → ℝ) (R : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hv : ∀ n, 0 ≤ v n)
    (hstep : ∀ n, dist (x (n + 1)) (x n) ≤ a (n + 1))
    (hlocal : ∀ n, dist (x n) z < R →
      2 * a (n + 1) ≤ a n + v n - v (n + 1))
    (hstart : dist (x 0) z + a 0 + v 0 < R) :
    Summable (fun n => dist (x (n + 1)) (x n)) ∧
      ∃ l, Tendsto x atTop (𝓝 l) := by
  have hs := local_trapping_summable x z a v R ha hv hstep hlocal hstart
  have hd : Summable (fun n => dist (x (n + 1)) (x n)) :=
    hs.of_nonneg_of_le (fun _ => dist_nonneg) hstep
  refine ⟨hd, cauchySeq_tendsto_of_complete ?_⟩
  apply cauchySeq_of_dist_le_of_summable (fun n => a (n + 1))
  · intro n
    simpa only [dist_comm] using hstep n
  · exact hs

end ProxLoj.Conv.PLFresh


open Filter Topology

namespace ProxLoj.Conv.PLFresh

theorem tail_trapping_converges {E : Type*} [MetricSpace E] [CompleteSpace E]
    (x : ℕ → E) (z : E) (a v : ℕ → ℝ) (R : ℝ) (N : ℕ)
    (ha : ∀ n, 0 ≤ a n) (hv : ∀ n, 0 ≤ v n)
    (hstep : ∀ n, dist (x (n + 1)) (x n) ≤ a (n + 1))
    (hlocal : ∀ n, N ≤ n → dist (x n) z < R →
      2 * a (n + 1) ≤ a n + v n - v (n + 1))
    (hstart : dist (x N) z + a N + v N < R) :
    Summable (fun n => dist (x (n + 1)) (x n)) ∧
      ∃ l, Tendsto x atTop (𝓝 l) := by
  have ht := local_trapping_converges (fun n => x (n + N)) z
    (fun n => a (n + N)) (fun n => v (n + N)) R
    (fun n => ha _) (fun n => hv _)
    (fun n => by simpa only [Nat.add_right_comm] using hstep (n + N))
    (fun n h => by simpa only [Nat.add_right_comm] using hlocal (n + N) (by omega) h)
    (by simpa only [Nat.zero_add] using hstart)
  have hs : Summable (fun n => dist (x (n + 1)) (x n)) := by
    have h := ht.1
    simp only [Nat.add_right_comm] at h
    exact (summable_nat_add_iff N).mp h
  refine ⟨hs, cauchySeq_tendsto_of_complete ?_⟩
  apply cauchySeq_of_summable_dist
  simpa only [dist_comm] using hs

theorem exists_trapping_index {E : Type*} [PseudoMetricSpace E]
    (x : ℕ → E) (z : E) (a v : ℕ → ℝ) (R : ℝ)
    (hR : 0 < R) (ha : Tendsto a atTop (𝓝 0))
    (hv : Tendsto v atTop (𝓝 0)) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) (hx : Tendsto (fun n => x (φ n)) atTop (𝓝 z)) :
    ∃ N, 1 ≤ N ∧ dist (x N) z + a N + v N < R := by
  have ht : Tendsto (fun n => dist (x (φ n)) z + a (φ n) + v (φ n))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, dist_self, add_zero] using
      (hx.dist (tendsto_const_nhds (x := z))).add (ha.comp hφ.tendsto_atTop) |>.add
        (hv.comp hφ.tendsto_atTop)
  have he := ht.eventually (gt_mem_nhds hR)
  have hn := hφ.tendsto_atTop.eventually (eventually_ge_atTop 1)
  obtain ⟨n, hn, he⟩ := (hn.and he).exists
  exact ⟨φ n, hn, he⟩

theorem cluster_trapping_converges {E : Type*} [MetricSpace E] [CompleteSpace E]
    (x : ℕ → E) (z : E) (a v : ℕ → ℝ) (R : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hv : ∀ n, 0 ≤ v n)
    (hstep : ∀ n, dist (x (n + 1)) (x n) ≤ a (n + 1))
    (hlocal : ∀ n, 1 ≤ n → dist (x n) z < R →
      2 * a (n + 1) ≤ a n + v n - v (n + 1))
    (hR : 0 < R) (ha0 : Tendsto a atTop (𝓝 0))
    (hv0 : Tendsto v atTop (𝓝 0)) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) (hx : Tendsto (fun n => x (φ n)) atTop (𝓝 z)) :
    Summable (fun n => dist (x (n + 1)) (x n)) ∧ Tendsto x atTop (𝓝 z) := by
  obtain ⟨N, hN, hstart⟩ := exists_trapping_index x z a v R hR ha0 hv0 φ hφ hx
  obtain ⟨hs, l, hl⟩ := tail_trapping_converges x z a v R N ha hv hstep
    (fun n hn => hlocal n (hN.trans hn)) hstart
  have he : l = z := tendsto_nhds_unique (hl.comp hφ.tendsto_atTop) hx
  exact ⟨hs, he ▸ hl⟩

end ProxLoj.Conv.PLFresh


namespace ProxLoj.Conv.PLFresh

theorem rpow_desingularization {x y θ : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    (1 - θ) * (x - y) ≤ x ^ θ * (x ^ (1 - θ) - y ^ (1 - θ)) := by
  have hp : 0 < 1 - θ := by linarith
  have hb := rpow_one_add_le_one_add_mul_self
    (s := y / x - 1) (by have := div_nonneg hy hx.le; linarith : -1 ≤ y / x - 1) hp.le (by linarith : 1 - θ ≤ 1)
  rw [add_sub_cancel, Real.div_rpow hy hx.le] at hb
  have hxpow : 0 < x ^ (1 - θ) := Real.rpow_pos_of_pos hx _
  have h := (div_le_iff₀ hxpow).mp hb
  have hmul := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hx.le θ)
  have he : x ^ θ * x ^ (1 - θ) = x := by
    rw [← Real.rpow_add hx]
    simp
  have hr : x ^ θ * ((1 + (1 - θ) * (y / x - 1)) * x ^ (1 - θ)) =
      x - (1 - θ) * (x - y) := by
    calc
      _ = (x ^ θ * x ^ (1 - θ)) * (1 + (1 - θ) * (y / x - 1)) := by ring
      _ = x - (1 - θ) * (x - y) := by rw [he]; field_simp; ring
  rw [hr] at hmul
  nlinarith [he]

theorem length_recurrence {a b A d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : 0 ≤ A) (hd : 0 ≤ d) (h : b ^ 2 ≤ A * a * d) :
    2 * b ≤ a + A * d := by
  have hc : 0 ≤ A * d := mul_nonneg hA hd
  have hsq : (2 * b) ^ 2 ≤ (a + A * d) ^ 2 := by
    nlinarith [sq_nonneg (a - A * d)]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq

end ProxLoj.Conv.PLFresh


namespace ProxLoj.Conv.PLFresh

theorem local_length_recurrence {x y θ a b D C : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hyx : y ≤ x)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hD : 0 < D) (hC : 0 ≤ C)
    (hdescent : b ^ 2 ≤ D * (x - y))
    (hloj : 0 < x → x ^ θ ≤ C * a) :
    2 * b ≤ a + (D * C / (1 - θ)) *
      (x ^ (1 - θ) - y ^ (1 - θ)) := by
  have hp : 0 < 1 - θ := by linarith
  have hd : 0 ≤ x ^ (1 - θ) - y ^ (1 - θ) := by
    exact sub_nonneg.mpr (Real.rpow_le_rpow hy hyx hp.le)
  by_cases hx0 : x = 0
  · have hy0 : y = 0 := by linarith
    have hb0 : b = 0 := by nlinarith
    simp only [hx0, hy0, hb0, sub_self, mul_zero, add_zero]
    exact ha
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have ht := rpow_desingularization hxpos hy hθ0 hθ1
    have hl := mul_le_mul_of_nonneg_right (hloj hxpos) hd
    have h1 := mul_le_mul_of_nonneg_left hdescent hp.le
    have h2 := mul_le_mul_of_nonneg_left (ht.trans hl) hD.le
    have hsq : b ^ 2 ≤ (D * C / (1 - θ)) * a *
        (x ^ (1 - θ) - y ^ (1 - θ)) := by
      have he : ((D * C / (1 - θ)) * a *
          (x ^ (1 - θ) - y ^ (1 - θ))) * (1 - θ) =
          D * C * a * (x ^ (1 - θ) - y ^ (1 - θ)) := by
        field_simp
      apply (mul_le_mul_iff_left₀ hp).mp
      rw [he]
      nlinarith
    exact length_recurrence ha hb (by positivity) hd hsq

end ProxLoj.Conv.PLFresh


open Filter Topology

namespace ProxLoj.Conv.PLFresh

theorem lojasiewicz_sequence_converges {E : Type*} [MetricSpace E] [CompleteSpace E]
    (x : ℕ → E) (z : E) (a e : ℕ → ℝ) (R D C θ : ℝ)
    (ha : ∀ n, 0 ≤ a n) (he : ∀ n, 0 ≤ e n)
    (hmono : ∀ n, e (n + 1) ≤ e n)
    (hstep : ∀ n, dist (x (n + 1)) (x n) ≤ a (n + 1))
    (hdescent : ∀ n, 1 ≤ n → a (n + 1) ^ 2 ≤ D * (e n - e (n + 1)))
    (hloj : ∀ n, 1 ≤ n → dist (x n) z < R → 0 < e n → (e n) ^ θ ≤ C * a n)
    (hR : 0 < R) (hD : 0 < D) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (ha0 : Tendsto a atTop (𝓝 0)) (he0 : Tendsto e atTop (𝓝 0))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hx : Tendsto (fun n => x (φ n)) atTop (𝓝 z)) :
    Summable (fun n => dist (x (n + 1)) (x n)) ∧ Tendsto x atTop (𝓝 z) := by
  let A := D * C / (1 - θ)
  have hp : 0 < 1 - θ := by linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hv0 : Tendsto (fun n => A * (e n) ^ (1 - θ)) atTop (𝓝 0) := by
    have hpow := (Real.continuousAt_rpow_const 0 (1 - θ) (Or.inr hp.le)).tendsto.comp he0
    simpa only [Function.comp_def, Real.zero_rpow hp.ne', mul_zero] using hpow.const_mul A
  apply cluster_trapping_converges x z a (fun n => A * (e n) ^ (1 - θ)) R ha
    (fun n => mul_nonneg hA (Real.rpow_nonneg (he n) _)) hstep
    ?_ hR ha0 hv0 φ hφ hx
  intro n hn hnear
  have h := local_length_recurrence (he n) (he (n + 1)) (hmono n)
    hθ0 hθ1 (ha n) (ha (n + 1)) hD hC (hdescent n hn) (hloj n hn hnear)
  dsimp only [A]
  nlinarith

end ProxLoj.Conv.PLFresh


open Filter Topology NonconvexSplitting.Shared NonsmoothLojasiewicz.Continuous
namespace ProxLoj.Conv.PLFresh

theorem native_theorem_4 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hproper : IsProper f) (hlsc : LowerSemicontinuous f)
    (hH1 : H1 f) (hH2 : H2 f) (hH3 : HasLojProperty f)
    (lam : ℕ → ℝ) (lamMinus lamPlus : ℝ) (hstep : StepBounds lam lamMinus lamPlus)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsProxRun f lam x)
    (hbdd : Bornology.IsBounded (Set.range x)) :
    Summable (fun k => ‖x (k + 1) - x k‖) ∧
      ∃ xinf ∈ crit f, Tendsto x atTop (𝓝 xinf) := by
  obtain ⟨l, hl, hlow⟩ := exists_energy_limit hproper hx hstep hH1
  obtain ⟨z, hzcrit, _, hzvalue, φ, hφ, hconv⟩ :=
    exists_critical_cluster hproper hlsc hH2 hx hstep hbdd hl
  obtain ⟨C, R, θ, hC, hR, hθ0, hθ1, hloj⟩ := hH3 z hzcrit
  let y : ℕ → EuclideanSpace ℝ (Fin n) := fun k => x (k + 1)
  let a : ℕ → ℝ := fun k => ‖y k - y (k - 1)‖
  let e : ℕ → ℝ := fun k => (f (y k)).toReal - l
  have he : ∀ k, 0 ≤ e k := fun k => sub_nonneg.mpr (hlow k)
  have ha0 : Tendsto a atTop (𝓝 0) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [a, y, Nat.add_sub_cancel] using tail_step_tendsto_zero hproper hx hstep hl
  have he0 : Tendsto e atTop (𝓝 0) := by
    simpa only [e, y, sub_self] using hl.sub_const l
  have hmono : ∀ k, e (k + 1) ≤ e k := by
    intro k
    exact sub_le_sub_right (energy_antitone hproper hx hstep (Nat.le_succ k)) l
  have hdist : ∀ k, dist (y (k + 1)) (y k) ≤ a (k + 1) := by
    intro k
    simp only [a, Nat.add_sub_cancel, dist_eq_norm, le_refl]
  have hd : ∀ k, 1 ≤ k → a (k + 1) ^ 2 ≤ (2 * lamPlus) * (e k - e (k + 1)) := by
    intro k _
    simpa only [a, y, e, Nat.add_sub_cancel, sub_sub_sub_cancel_right] using
      step_square_bound hproper hx hstep k
  have hlocal : ∀ k, 1 ≤ k → dist (y k) z < R → 0 < e k →
      (e k) ^ θ ≤ (C / lamMinus) * a k := by
    intro k hk hnear hepos
    have hsub := prox_limiting hproper hx k (step_pos hstep k)
    have hq := hloj (y k) hnear (proxVector lam x k) hsub
    have hval : |(f (y k)).toReal - (f z).toReal| = e k := by
      rw [hzvalue]
      exact abs_of_nonneg (he k)
    rw [hval, lojPow, if_neg (ne_of_gt hepos)] at hq
    have hki : k - 1 + 1 = k := Nat.sub_add_cancel hk
    have hlamp := step_pos hstep k
    have hinv : (lam k)⁻¹ ≤ lamMinus⁻¹ := inv_anti₀ hstep.1 (hstep.2.2 k).1.le
    have hn : ‖proxVector lam x k‖ ≤ lamMinus⁻¹ * a k := by
      simpa only [proxVector, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hlamp,
        a, y, hki, norm_sub_rev] using
        mul_le_mul_of_nonneg_right hinv (norm_nonneg (x (k + 1) - x k))
    calc
      (e k) ^ θ ≤ C * ‖proxVector lam x k‖ := hq
      _ ≤ C * (lamMinus⁻¹ * a k) := mul_le_mul_of_nonneg_left hn hC.le
      _ = (C / lamMinus) * a k := by ring
  have hD : 0 < 2 * lamPlus := mul_pos (by norm_num) (hstep.1.trans hstep.2.1)
  obtain ⟨hsum, hy⟩ := lojasiewicz_sequence_converges y z a e R (2 * lamPlus)
    (C / lamMinus) θ (fun k => norm_nonneg _) he hmono hdist hd hlocal
    hR hD (div_nonneg hC.le hstep.1.le) hθ0 hθ1 ha0 he0 φ hφ hconv
  constructor
  · apply (summable_nat_add_iff 1).mp
    simpa only [y, dist_eq_norm] using hsum
  · refine ⟨z, hzcrit, ?_⟩
    exact (tendsto_add_atTop_iff_nat 1).mp hy

end ProxLoj.Conv.PLFresh


open Filter Topology NonconvexSplitting.Shared NonsmoothLojasiewicz.Continuous

namespace ProxLoj.Conv

/-- Theorem 4 (Convergence result), p. 5: if `f` is proper, lower semicontinuous and satisfies
(H1), (H2), (H3), every bounded proximal run has finite length and converges to a critical
point of `f`. -/
theorem theorem_4 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hproper : IsProper f) (hlsc : LowerSemicontinuous f)
    (hH1 : H1 f) (hH2 : H2 f) (hH3 : HasLojProperty f)
    (lam : ℕ → ℝ) (lamMinus lamPlus : ℝ) (hstep : StepBounds lam lamMinus lamPlus)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsProxRun f lam x)
    (hbdd : Bornology.IsBounded (Set.range x)) :
    Summable (fun k => ‖x (k + 1) - x k‖) ∧
      ∃ xinf ∈ crit f, Tendsto x atTop (𝓝 xinf) := by
  exact PLFresh.native_theorem_4 f hproper hlsc hH1 hH2 hH3 lam lamMinus lamPlus hstep x hx hbdd

end ProxLoj.Conv

open Filter Topology NonconvexSplitting.Shared NonsmoothLojasiewicz.Continuous ProxLoj.Conv

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hproper : IsProper f) (hlsc : LowerSemicontinuous f)
    (hH1 : H1 f) (hH2 : H2 f) (hH3 : HasLojProperty f)
    (lam : ℕ → ℝ) (lamMinus lamPlus : ℝ) (hstep : StepBounds lam lamMinus lamPlus)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsProxRun f lam x)
    (hbdd : Bornology.IsBounded (Set.range x)) :
    Summable (fun k => ‖x (k + 1) - x k‖) ∧
      ∃ xinf ∈ crit f, Tendsto x atTop (𝓝 xinf) := by
  exact ProxLoj.Conv.theorem_4 f hproper hlsc hH1 hH2 hH3 lam lamMinus lamPlus hstep x hx hbdd
