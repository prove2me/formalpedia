-- Prove2me | solution 1 for PVM.tendsto_simpleIntegral_of_tendstoUniformly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:44.437896+00:00
-- url     : https://prove2.me/submissions/6bf72bf1-54fe-44c1-b647-d4374f5f291e

import Definitions.Def_Spectral_PVM_Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.UniformSpace.Dini
import Definitions.Def_Spectral_PVM_Integral
import Theorems.Thm_PVM_norm_simpleIntegral_sub_le
section
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
private theorem nearestError_continuous (e : ℕ → ℂ) :
    ∀ n, Continuous (nearestError e n)
  | 0 => continuous_const.dist continuous_id
  | n + 1 => (continuous_const.dist continuous_id).min (nearestError_continuous e n)
private theorem nearestError_eq (e : ℕ → ℂ) (n : ℕ) (z : ℂ) :
    nearestError e n z = dist (SimpleFunc.nearestPt e n z) z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change min (dist (e (n + 1)) z) (nearestError e n z) = _
      rw [ih]
      simp only [SimpleFunc.nearestPt, SimpleFunc.nearestPtInd_succ,
        SimpleFunc.map_apply]
      split_ifs with h
      · rw [min_eq_left]
        have hle := (h (SimpleFunc.nearestPtInd e n z)
          (SimpleFunc.nearestPtInd_le e n z)).le
        rw [edist_dist, edist_dist] at hle
        exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hle
      · rw [min_eq_right]
        push Not at h
        obtain ⟨k, hk, hnew⟩ := h
        have hold := SimpleFunc.edist_nearestPt_le e z hk
        rw [edist_dist, edist_dist] at hold hnew
        exact ((ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hold).trans
          ((ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hnew)
private theorem nearestError_antitone (e : ℕ → ℂ) (z : ℂ) :
    Antitone (fun n => nearestError e n z) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [nearestError]
  exact min_le_right _ _
private theorem nearestError_tendsto_of_nearestPt_tendsto (e : ℕ → ℂ) (z : ℂ)
    (h : Filter.Tendsto (fun n => SimpleFunc.nearestPt e n z) Filter.atTop (nhds z)) :
    Filter.Tendsto (fun n => nearestError e n z) Filter.atTop (nhds 0) := by
  have hconst : Filter.Tendsto (fun _ : ℕ => z) Filter.atTop (nhds z) :=
    tendsto_const_nhds
  have hdist := h.dist hconst
  simpa only [nearestError_eq, dist_self] using hdist
private theorem nearestPt_tendstoUniformlyOn (s : Set ℂ) (hs : IsCompact s)
    (y₀ : ℂ) (hy₀ : y₀ ∈ s) :
    TendstoUniformlyOn
      (fun n z => SimpleFunc.approxOn id measurable_id s y₀ hy₀ n z)
      id Filter.atTop s := by
  let _ : Nonempty s := ⟨⟨y₀, hy₀⟩⟩
  let e : ℕ → ℂ := fun k => Nat.casesOn k y₀
    (Subtype.val ∘ TopologicalSpace.denseSeq s)
  have hpoint (z : ℂ) (hz : z ∈ s) :
      Filter.Tendsto (fun n => nearestError e n z) Filter.atTop (nhds 0) := by
    apply nearestError_tendsto_of_nearestPt_tendsto
    have h := SimpleFunc.tendsto_approxOn (f := id) measurable_id hy₀ (subset_closure hz)
    change Filter.Tendsto (fun n => SimpleFunc.nearestPt e n z) Filter.atTop (nhds z) at h
    exact h
  have hDini : TendstoUniformlyOn (fun n => nearestError e n) (fun _ => 0)
      Filter.atTop s :=
    Antitone.tendstoUniformlyOn_of_forall_tendsto hs
      (fun n => (nearestError_continuous e n).continuousOn)
      (fun z hz => nearestError_antitone e z) continuousOn_const hpoint
  rw [Metric.tendstoUniformlyOn_iff] at hDini ⊢
  intro ε hε
  filter_upwards [hDini ε hε] with n hn
  intro z hz
  have herr := hn z hz
  rw [dist_comm, Real.dist_0_eq_abs,
    abs_of_nonneg (by rw [nearestError_eq]; exact dist_nonneg)] at herr
  change dist z (SimpleFunc.nearestPt e n z) < ε
  rw [dist_comm, ← nearestError_eq]
  exact herr
private theorem boundedApprox_tendstoUniformly (f : ℝ → ℂ) (hf : Measurable f)
    (C : ℝ) (hbdd : ∀ t, ‖f t‖ ≤ C) :
    TendstoUniformly (fun n t => boundedApprox f hf C hbdd n t) f Filter.atTop := by
  have hzero : (0 : ℂ) ∈ Metric.closedBall 0 C :=
    Metric.mem_closedBall.mpr (by rw [dist_self]; exact bound_nonneg hbdd)
  have hU := nearestPt_tendstoUniformlyOn (Metric.closedBall (0 : ℂ) C)
    (ProperSpace.isCompact_closedBall 0 C) 0 hzero
  rw [Metric.tendstoUniformlyOn_iff] at hU
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hU ε hε] with n hn
  intro t
  have hft : f t ∈ Metric.closedBall (0 : ℂ) C := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hbdd t
  have h := hn (f t) hft
  change dist (f t) (boundedApprox f hf C hbdd n t) < ε
  exact h
private theorem simpleIntegral_boundedApprox_cauchy (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hbdd : ∀ t, ‖f t‖ ≤ C) :
    CauchySeq (fun n => E_pvm.simpleIntegral (boundedApprox f hf C hbdd n)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hU := boundedApprox_tendstoUniformly f hf C hbdd
  rw [Metric.tendstoUniformly_iff] at hU
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hU (ε / 4) (by linarith))
  refine ⟨N, ?_⟩
  intro m hm n hn
  rw [dist_eq_norm]
  have hpoint : ∀ t,
      ‖boundedApprox f hf C hbdd m t - boundedApprox f hf C hbdd n t‖ ≤ ε / 2 := by
    intro t
    apply le_of_lt
    calc
      ‖boundedApprox f hf C hbdd m t - boundedApprox f hf C hbdd n t‖ =
          dist (boundedApprox f hf C hbdd m t) (boundedApprox f hf C hbdd n t) := by
        rw [dist_eq_norm]
      _ ≤ dist (boundedApprox f hf C hbdd m t) (f t) +
          dist (f t) (boundedApprox f hf C hbdd n t) := dist_triangle _ _ _
      _ < ε / 4 + ε / 4 := by
        apply add_lt_add
        · rw [dist_comm]
          exact hN m hm t
        · exact hN n hn t
      _ = ε / 2 := by ring
  have hop := E_pvm.norm_simpleIntegral_sub_le
    (boundedApprox f hf C hbdd m) (boundedApprox f hf C hbdd n)
    (C := ε / 2) hpoint
  exact hop.trans_lt (by linarith)
private theorem PVM.tendsto_integralApprox (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ t, ‖f t‖ ≤ C) :
    Filter.Tendsto
      (fun n => E_pvm.simpleIntegral
        (boundedApprox f hf (Classical.choose hbdd) (Classical.choose_spec hbdd) n))
      Filter.atTop (nhds (E_pvm.integral f hf hbdd)) := by
  rw [PVM.integral]
  exact (simpleIntegral_boundedApprox_cauchy E_pvm f hf
    (Classical.choose hbdd) (Classical.choose_spec hbdd)).tendsto_limUnder
end

set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (s : ℕ → SimpleFunc ℝ ℂ)
    (hs : TendstoUniformly (fun n t => s n t) f Filter.atTop) :
    Filter.Tendsto (fun n => E_pvm.simpleIntegral (s n))
      Filter.atTop (nhds (E_pvm.integral f hf hbdd)) := by
  apply (E_pvm.tendsto_integralApprox f hf hbdd).congr_dist
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hUchosen := boundedApprox_tendstoUniformly f hf
    (Classical.choose hbdd) (Classical.choose_spec hbdd)
  rw [Metric.tendstoUniformly_iff] at hUchosen hs
  filter_upwards [hUchosen (ε / 4) (by linarith), hs (ε / 4) (by linarith)]
    with n hnchosen hn
  rw [Real.dist_0_eq_abs, abs_of_nonneg dist_nonneg, dist_eq_norm]
  have hpoint : ∀ t,
      ‖boundedApprox f hf (Classical.choose hbdd) (Classical.choose_spec hbdd) n t -
          s n t‖ ≤ ε / 2 := by
    intro t
    apply le_of_lt
    calc
      ‖boundedApprox f hf (Classical.choose hbdd) (Classical.choose_spec hbdd) n t -
          s n t‖ =
          dist (boundedApprox f hf (Classical.choose hbdd) (Classical.choose_spec hbdd) n t)
            (s n t) := by
        rw [dist_eq_norm]
      _ ≤ dist
          (boundedApprox f hf (Classical.choose hbdd) (Classical.choose_spec hbdd) n t) (f t) +
          dist (f t) (s n t) := dist_triangle _ _ _
      _ < ε / 4 + ε / 4 := by
        apply add_lt_add
        · rw [dist_comm]
          exact hnchosen t
        · exact hn t
      _ = ε / 2 := by ring
  exact (E_pvm.norm_simpleIntegral_sub_le
    (boundedApprox f hf (Classical.choose hbdd) (Classical.choose_spec hbdd) n)
    (s n) hpoint).trans_lt (by linarith)
end PVM
