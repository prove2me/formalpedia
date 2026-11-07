-- Prove2me | solution 1 for WaitJudge.Convex.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T23:26:46.646206+00:00
-- url     : https://prove2.me/submissions/7c4de93a-b2a6-4371-bf31-bf6067c48ba2

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_WaitJudge_Convex_Setting
import Theorems.Thm_WaitJudge_Convex_prob_violation_eq_sum_integral
import Theorems.Thm_WaitJudge_Convex_moment_conditions
import Theorems.Thm_WaitJudge_Convex_weak_duality
import Theorems.Thm_WaitJudge_Convex_iteratedDeriv_pow_div_factorial
import Theorems.Thm_WaitJudge_Convex_inf_poly_eq_gammaStar

open MeasureTheory ScenarioApproach.Generalization WaitJudge.Convex

theorem solution {d p : ℕ} {Δ : Type*} [MeasurableSpace Δ] (P : Measure Δ) [IsProbabilityMeasure P]
    (c : E d) (X : Set (E d)) (Xδ : Δ → Set (E d)) (tb : Fin p → E d → ℝ)
    (hX : Convex ℝ X) (hXδ : ∀ δ, Convex ℝ (Xδ δ))
    (htb : ∀ j, ConvexOn ℝ Set.univ (tb j))
    (hA1 : Assumption1 c X Xδ tb) (hA2 : Assumption2 c X Xδ tb P)
    (hmeas : MeasurabilityPins c X Xδ tb)
    (N : ℕ) (hN : d < N) (ε : ℕ → ℝ) (hε : ∀ k ≤ d, 0 ≤ ε k ∧ ε k ≤ 1) :
    (Measure.pi fun _ : Fin N => P) {ω | ε (sstar c X Xδ tb ω) < violation P Xδ (xstar c X Xδ tb ω)} ≤ ENNReal.ofReal (gammaStar N d ε) := by
  -- (1/k!) D^k of a polynomial written in the monomial basis, via (23)
  have key : ∀ (q : Polynomial ℝ) (M : ℕ), q.natDegree < M + 1 → ∀ (k : ℕ) (t : ℝ),
      (1 / (k.factorial : ℝ)) * iteratedDeriv k (fun t => q.eval t) t =
        ∑ m ∈ Finset.Icc k M, q.coeff m * (m.choose k : ℝ) * t ^ (m - k) := by
    intro q M hM k t
    have hfun : (fun t => q.eval t) = fun t => ∑ m ∈ Finset.range (M + 1), q.coeff m * t ^ m := by
      funext t; exact Polynomial.eval_eq_sum_range' hM t
    rw [hfun, iteratedDeriv_fun_sum (fun i _ => by fun_prop), Finset.mul_sum]
    have h1 : ∀ m ∈ Finset.range (M + 1), (1 / (k.factorial : ℝ)) *
        iteratedDeriv k (fun t => q.coeff m * t ^ m) t =
          if m < k then 0 else q.coeff m * (m.choose k : ℝ) * t ^ (m - k) := by
      intro m _
      rw [iteratedDeriv_const_mul_field, mul_left_comm, iteratedDeriv_pow_div_factorial]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl h1, Finset.sum_ite, Finset.sum_const_zero, zero_add]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext m; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
  have hpoly : ∀ (q : Polynomial ℝ) (n : WithTop ℕ∞), ContDiff ℝ n (fun t => q.eval t) :=
    fun q n => by
      have hfun : (fun t => q.eval t) =
          fun t => ∑ m ∈ Finset.range (q.natDegree + 1), q.coeff m * t ^ m := by
        funext t; exact Polynomial.eval_eq_sum_range' (Nat.lt_succ_self _) t
      rw [hfun]; fun_prop
  have : ∀ k, IsFiniteMeasure (Fk P c X Xδ tb k) := fun k => by unfold Fk; infer_instance
  have hIcc : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  rw [prob_violation_eq_sum_integral P c X Xδ tb hX hXδ htb hA1 hA2 hmeas N hN ε hε]
  apply ENNReal.ofReal_le_ofReal
  rw [← inf_poly_eq_gammaStar N d ε hε]
  apply le_csInf
  · -- the polynomial t ^ N is feasible for (10)
    refine ⟨_, Polynomial.X ^ N, ⟨?_, ?_⟩, rfl⟩
    · exact (hpoly _ d).contDiffOn
    · intro k hk t ht
      have hcd : ContDiffAt ℝ k (fun t => (Polynomial.X ^ N : Polynomial ℝ).eval t) t :=
        (hpoly _ k).contDiffAt
      rw [iteratedDerivWithin_eq_iteratedDeriv hIcc hcd ht]
      have hfun : (fun t => (Polynomial.X ^ N : Polynomial ℝ).eval t) = fun t => t ^ N := by
        funext t; simp
      rw [hfun, iteratedDeriv_pow_div_factorial, if_neg (by omega)]
      have h0 : 0 ≤ (N.choose k : ℝ) * t ^ (N - k) := by
        have := ht.1; positivity
      have hind : Set.indicator (Set.Ico 0 (1 - ε k)) (1 : ℝ → ℝ) t ≤ 1 := by
        unfold Set.indicator; split_ifs <;> simp
      calc (N.choose k : ℝ) * t ^ (N - k) * Set.indicator (Set.Ico 0 (1 - ε k)) 1 t
          ≤ (N.choose k : ℝ) * t ^ (N - k) * 1 := mul_le_mul_of_nonneg_left hind h0
        _ = _ := mul_one _
  · rintro y ⟨q, hq, rfl⟩
    set M := max d q.natDegree with hMdef
    have hM : q.natDegree < M + 1 := by omega
    have hlam : ∀ k ≤ d, ∀ v ∈ Set.Icc (0 : ℝ) 1,
        (N.choose k : ℝ) * (1 - v) ^ (N - k) * Set.indicator (Set.Ioc (ε k) 1) 1 v ≤
          ∑ m ∈ Finset.Icc k M, q.coeff m * (m.choose k : ℝ) * (1 - v) ^ (m - k) := by
      intro k hk v hv
      have ht : (1 - v) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hv.2], by linarith [hv.1]⟩
      have h := hq.2 k hk (1 - v) ht
      have hcd : ContDiffAt ℝ k (fun t => q.eval t) (1 - v) :=
        (hpoly q k).contDiffAt
      rw [iteratedDerivWithin_eq_iteratedDeriv hIcc hcd ht, key q M hM k] at h
      have hind : Set.indicator (Set.Ioc (ε k) 1) (1 : ℝ → ℝ) v =
          Set.indicator (Set.Ico 0 (1 - ε k)) (1 : ℝ → ℝ) (1 - v) := by
        unfold Set.indicator
        by_cases h1 : ε k < v
        · rw [if_pos ⟨h1, hv.2⟩, if_pos ⟨by linarith [hv.2], by linarith⟩]; rfl
        · rw [if_neg (fun h' => h1 h'.1), if_neg (fun h' => h1 (by linarith [h'.2]))]
      rw [hind]; exact h
    have hwd := weak_duality d M N (le_max_left _ _) ε hε (Fk P c X Xδ tb)
      (fun m _ => moment_conditions P c X Xδ tb hX hXδ htb hA1 hA2 hmeas m) (fun m => q.coeff m) hlam
    rw [Polynomial.eval_eq_sum_range' hM 1]
    simpa using hwd
