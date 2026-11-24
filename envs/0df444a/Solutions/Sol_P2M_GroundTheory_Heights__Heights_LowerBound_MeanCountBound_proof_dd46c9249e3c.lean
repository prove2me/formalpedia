-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBound_MeanCountBound_proof_dd46c9249e3c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:50:17.446903+00:00
-- url     : https://prove2.me/submissions/05d46148-c45e-45a5-95eb-39803e8c65b5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PMeanCountBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBound
open Real MeasureTheory Filter Topology Finset
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.LowerBound
namespace MeanCountBound
theorem _root_.solution : MeanCountBound.Statement := by
  intro X _ μ lam cnt a ka r h
  have := h.isProbability
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 1 / 12 := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; norm_num
  have hθ1 : θ ≤ 1 := by rw [hθ]; norm_num
  have hθ12 : 12 * θ = 1 := by rw [hθ]; norm_num
  have hr := h.r_pos
  have ha0 : a ≠ 0 := by have := h.one_le_a; omega
  set m := meanCount μ cnt r with hm
  have hm0 : 0 ≤ m := integral_nonneg (h.cnt_nonneg r)
  have hprod : ∀ j : ℕ, (12 : ℝ) ^ j * θ ^ j = 1 := fun j => by
    rw [← mul_pow, hθ12, one_pow]

  have hpt : ∀ (j : ℕ) (z : X), lam z < r → θ ^ (j + 1) * r ≤ lam z →
      cnt r z ≤ (3 * 12 ^ (j + 1)) ^ a := by
    intro j z hlt hle
    have hl := h.lam_pos z
    calc cnt r z ≤ (3 * r / lam z) ^ a := h.count r hr le_rfl z hlt
      _ ≤ (3 * 12 ^ (j + 1)) ^ a := by
        gcongr
        rw [div_le_iff₀ hl]
        calc 3 * r = 3 * 12 ^ (j + 1) * (θ ^ (j + 1) * r) := by
              linear_combination (-(3 * r)) * hprod (j + 1)
          _ ≤ 3 * 12 ^ (j + 1) * lam z := by gcongr

  have hterm : ∀ k : ℕ, (36 * 12 ^ (k + 1) : ℝ) ^ a * meanCount μ cnt (θ ^ (k + 1) * r)
      ≤ 1 / 4 * (1 / 2) ^ k * m := by
    intro k
    have hy0 : 0 < θ ^ (k + 1) := pow_pos hθ0 _
    have hy1 : θ ^ (k + 1) ≤ 1 := pow_le_one₀ hθ0.le hθ1
    rw [h.scaling _ _ hy0 hr, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hm0
    have hka : (θ ^ (k + 1)) ^ ka ≤ (θ ^ (k + 1)) ^ (3 * a) := by
      rw [← Real.rpow_natCast (θ ^ (k + 1)) (3 * a)]
      apply Real.rpow_le_rpow_of_exponent_ge hy0 hy1
      have := h.three_a_le_ka
      push_cast
      linarith
    have heq : (36 * 12 ^ (k + 1) : ℝ) ^ a * (θ ^ (k + 1)) ^ (3 * a)
        = (36 * (θ ^ (k + 1)) ^ 2) ^ a := by
      rw [pow_mul, ← mul_pow]
      congr 1
      linear_combination (36 * (θ ^ (k + 1)) ^ 2) * hprod (k + 1)
    have hsq : 36 * (θ ^ (k + 1)) ^ 2 = 1 / 4 * (θ ^ 2) ^ k := by
      have : θ ^ 2 = 1 / 144 := by rw [hθ]; norm_num
      rw [← pow_mul, show (k + 1) * 2 = 2 + 2 * k by ring, pow_add, pow_mul, this]
      ring
    have hθ2 : θ ^ 2 ≤ 1 / 2 := by rw [hθ]; norm_num
    have hs1 : 1 / 4 * (θ ^ 2) ^ k ≤ 1 / 4 * (1 / 2) ^ k := by gcongr
    have hs2 : 1 / 4 * (θ ^ 2) ^ k ≤ 1 := by
      calc 1 / 4 * (θ ^ 2) ^ k ≤ 1 / 4 * 1 := by
            gcongr; exact pow_le_one₀ (by positivity) (by linarith)
        _ ≤ 1 := by norm_num
    calc (36 * 12 ^ (k + 1) : ℝ) ^ a * (θ ^ (k + 1)) ^ ka
        ≤ (36 * 12 ^ (k + 1) : ℝ) ^ a * (θ ^ (k + 1)) ^ (3 * a) := by gcongr
      _ = (1 / 4 * (θ ^ 2) ^ k) ^ a := by rw [heq, hsq]
      _ ≤ 1 / 4 * (θ ^ 2) ^ k := pow_le_of_le_one (by positivity) hs2 ha0
      _ ≤ 1 / 4 * (1 / 2) ^ k := hs1

  let S : ℕ → Set X := fun N => {z | θ ^ (N + 1) * r ≤ lam z}
  have hSmeas : ∀ N, MeasurableSet (S N) := fun N =>
    measurableSet_le measurable_const h.lam_meas
  have hSmono : Monotone S := by
    intro N M hNM z hz
    simp only [S, Set.mem_ofPred_eq] at hz ⊢
    have : θ ^ (M + 1) ≤ θ ^ (N + 1) := pow_le_pow_of_le_one hθ0.le hθ1 (by omega)
    nlinarith
  have hSunion : ⋃ N, S N = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos (h.lam_pos z) hr)
      (show θ < 1 by rw [hθ]; norm_num)
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    simp only [S, Set.mem_ofPred_eq]
    have h1 : θ ^ (n + 1) ≤ θ ^ n := pow_le_pow_of_le_one hθ0.le hθ1 (by omega)
    rw [lt_div_iff₀ hr] at hn
    nlinarith

  have hbound : ∀ N, ∫ z in S N, cnt r z ∂μ ≤ 36 ^ a + m / 2 := by
    intro N
    set G : X → ℝ := fun z => 36 ^ a +
      ∑ i ∈ range N, (36 * 12 ^ (i + 1) : ℝ) ^ a * cnt (θ ^ (i + 1) * r) z with hG
    have hint : ∀ i : ℕ, Integrable (cnt (θ ^ (i + 1) * r)) μ := fun i =>
      h.integrable _ (mul_pos (pow_pos hθ0 _) hr)
    have hGi : Integrable G μ :=
      (integrable_const _).add (integrable_finsetSum _ fun i _ => (hint i).const_mul _)
    have hsum_nonneg : ∀ z, 0 ≤ ∑ i ∈ range N, (36 * 12 ^ (i + 1) : ℝ) ^ a *
        cnt (θ ^ (i + 1) * r) z := fun z =>
      sum_nonneg fun i _ => mul_nonneg (by positivity) (h.cnt_nonneg _ _)
    have hG0 : ∀ z, 0 ≤ G z := fun z => add_nonneg (by positivity) (hsum_nonneg z)
    have hle : ∀ z ∈ S N, cnt r z ≤ G z := by
      intro z hz
      simp only [S, Set.mem_ofPred_eq] at hz
      rcases le_or_gt r (lam z) with hrl | hlr
      · rw [h.zero r hr z hrl]; exact hG0 z
      classical
      have hex : ∃ j, θ ^ (j + 1) * r ≤ lam z := ⟨N, hz⟩
      set j := Nat.find hex with hj
      have hjle : j ≤ N := Nat.find_min' hex hz
      have hjspec : θ ^ (j + 1) * r ≤ lam z := Nat.find_spec hex
      rcases Nat.eq_zero_or_eq_succ_pred j with hj0 | hjs
      · calc cnt r z ≤ (3 * 12 ^ (j + 1)) ^ a := hpt j z hlr hjspec
          _ = 36 ^ a := by rw [hj0]; norm_num
          _ ≤ G z := le_add_of_nonneg_right (hsum_nonneg z)
      · set k := j.pred
        have hk : k < N := by omega
        have hnot : ¬ θ ^ (k + 1) * r ≤ lam z := Nat.find_min hex (by omega)
        have hone : 1 ≤ cnt (θ ^ (k + 1) * r) z :=
          h.one _ (mul_pos (pow_pos hθ0 _) hr)
            (mul_le_of_le_one_left hr.le (pow_le_one₀ hθ0.le hθ1)) z (lt_of_not_ge hnot)
        calc cnt r z ≤ (3 * 12 ^ (j + 1)) ^ a := hpt j z hlr hjspec
          _ = (36 * 12 ^ (k + 1) : ℝ) ^ a := by
              rw [hjs, Nat.succ_eq_add_one]; congr 1; ring
          _ ≤ (36 * 12 ^ (k + 1) : ℝ) ^ a * cnt (θ ^ (k + 1) * r) z :=
              le_mul_of_one_le_right (by positivity) hone
          _ ≤ ∑ i ∈ range N, (36 * 12 ^ (i + 1) : ℝ) ^ a * cnt (θ ^ (i + 1) * r) z :=
              single_le_sum (f := fun i => (36 * 12 ^ (i + 1) : ℝ) ^ a *
                cnt (θ ^ (i + 1) * r) z)
                (fun i _ => mul_nonneg (by positivity) (h.cnt_nonneg _ _))
                (mem_range.2 hk)
          _ ≤ G z := le_add_of_nonneg_left (by positivity)
    have hGint : ∫ z, G z ∂μ = 36 ^ a + ∑ i ∈ range N,
        (36 * 12 ^ (i + 1) : ℝ) ^ a * meanCount μ cnt (θ ^ (i + 1) * r) := by
      rw [hG, integral_add (integrable_const _)
        (integrable_finsetSum _ fun i _ => (hint i).const_mul _),
        integral_finsetSum _ fun i _ => (hint i).const_mul _]
      simp [integral_const_mul, meanCount]
    have hgeo : ∑ i ∈ range N, (36 * 12 ^ (i + 1) : ℝ) ^ a *
        meanCount μ cnt (θ ^ (i + 1) * r) ≤ m / 2 := by
      calc _ ≤ ∑ i ∈ range N, 1 / 4 * (1 / 2 : ℝ) ^ i * m := sum_le_sum fun i _ => hterm i
        _ = 1 / 4 * m * ∑ i ∈ range N, (1 / 2 : ℝ) ^ i := by
            rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
        _ ≤ 1 / 4 * m * 2 := by gcongr; exact sum_geometric_two_le N
        _ = m / 2 := by ring
    calc ∫ z in S N, cnt r z ∂μ ≤ ∫ z in S N, G z ∂μ :=
          setIntegral_mono_on (h.integrable r hr).integrableOn hGi.integrableOn (hSmeas N) hle
      _ ≤ ∫ z, G z ∂μ := setIntegral_le_integral hGi (ae_of_all _ hG0)
      _ ≤ 36 ^ a + m / 2 := by rw [hGint]; linarith
  have ht := tendsto_setIntegral_of_monotone hSmeas hSmono
    (by rw [hSunion]; exact (h.integrable r hr).integrableOn)
  rw [hSunion, Measure.restrict_univ] at ht
  have hfin : m ≤ 36 ^ a + m / 2 := le_of_tendsto' ht hbound
  linarith
end MeanCountBound
end GroundTheory.Heights₂.Heights.LowerBound
