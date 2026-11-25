-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundOfPrimeBound_proof_39800829bdbc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:51:48.246316+00:00
-- url     : https://prove2.me/submissions/55712984-c381-4883-b910-41b8dde02664

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsElem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PrimeWeightEqZeroOfLt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PRestBoundOfPrimeBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_ChebyshevThetaBound_intersectionNumber_baseChange_1e58a3fff588
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_primeWeight_nonneg_6255b916e79a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_prime_partial_le_66a4bd05bbf2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_ExponentialTail_intersectionNumber_baseChange_69f6990adeee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_GeometricTail_intersectionNumber_baseChange_cf5b94796824
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_IntegerLogSquareTail_intersectionNumber_baseChange_ca98df2fb43b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_PrimeLogSquareTail_intersectionNumber_baseChange_8bf873d99c93
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_RestConstants_intersectionNumber_baseChange_3cbe9c9bc2bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SmallRankBound_intersectionNumber_baseChange_63d64eced049
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SmallRankWeakHypothesis_intersectionNumber_baseChange_46cb8718a615
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_XBound_intersectionNumber_baseChange_3674cb61fc35
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_XOverPrime_intersectionNumber_baseChange_8ed2297f9f86
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_two_log_four_le_07c7efd7ce7c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open Finset Elem
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace RestBoundOfPrimeBound
theorem _root_.solution : RestBoundOfPrimeBound.Statement := by
  classical
  intro f r a c B₀ hf hr ha hB Q s e hp P
  set R : ℕ → ℝ := fun p => restPrimeModel f r a c Q s e p with hR
  set C : ℝ := ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)| with hC
  set X : ℝ := (restX r a : ℝ) with hXdef
  have hN2 : 2 ≤ r + a := by omega
  have hNR : (2 : ℝ) ≤ ((r + a : ℕ) : ℝ) := by exact_mod_cast hN2
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hB0 : 0 < B₀ := by nlinarith
  have hC0 : 0 ≤ C := by positivity
  have hX0 : 0 ≤ X := by
    simp only [hXdef, restX]; push_cast; positivity
  set K : ℝ := 1.5 * f * X * C with hK
  have hK0 : 0 ≤ K := by positivity
  set S : Set ℕ := {p | p ∈ P ∧ p.Prime ∧ B₀ < p} with hS
  set g : ℕ → ℝ := fun i => if i ∈ P ∧ i.Prime ∧ B₀ < i then |R i| else 0 with hg
  have hind : S.indicator (fun p => |R p|) = g := by
    funext i
    by_cases h : i ∈ P ∧ i.Prime ∧ B₀ < i
    · simp [hS, hg, Set.indicator_of_mem, h]
    · rw [Set.indicator_of_notMem (show i ∉ S from h)]
      simp [hg, h]
  have hg0 : ∀ i, 0 ≤ g i := fun i => by
    simp only [hg]; split_ifs <;> positivity
  have hgle : ∀ i, g i ≤ K * (primeWeight B₀ i / (i : ℝ) ^ 2) := fun i => by
    simp only [hg]
    split_ifs with h
    · have hw : primeWeight B₀ i = Real.log i := by simp [primeWeight, h.2.1, h.2.2]
      rw [hw]
      calc |R i| ≤ 1.5 * f * X * (Real.log i / (i : ℝ) ^ 2) * ((f * (r * a) + 1 : ℕ) : ℝ) *
            |(fibreDegree f r a c : ℝ)| := hp i h.2.1 h.2.2
        _ = K * (Real.log i / (i : ℝ) ^ 2) := by rw [hK, hC]; ring
    · exact mul_nonneg hK0 (div_nonneg (primeWeight_nonneg B₀ i) (by positivity))
  have hpart : ∀ n, ∑ i ∈ range n, g i ≤ K * (2 * Real.log 4 / B₀) := fun n => by
    calc ∑ i ∈ range n, g i ≤ ∑ i ∈ range n, K * (primeWeight B₀ i / (i : ℝ) ^ 2) :=
          Finset.sum_le_sum fun i _ => hgle i
      _ = K * ∑ i ∈ range n, primeWeight B₀ i / (i : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ K * (2 * Real.log 4 / B₀) :=
          mul_le_mul_of_nonneg_left (prime_partial_le B₀ hB0 n) hK0
  have hgs : Summable g := summable_of_sum_range_le hg0 hpart
  have hsub : Summable (fun p : S => |R p|) :=
    (summable_subtype_iff_indicator (f := fun p : ℕ => |R p|) (s := S)).mpr (by rw [hind]; exact hgs)
  refine ⟨hsub, ?_⟩
  have htsum : ∑' p : S, |R p| ≤ K * (2 * Real.log 4 / B₀) := by
    rw [tsum_subtype S (fun p : ℕ => |R p|), hind]
    exact Real.tsum_le_of_sum_range_le hg0 hpart
  have habs : |∑' p : S, R p| ≤ ∑' p : S, |R p| := by
    have := norm_tsum_le_tsum_norm (f := fun p : S => R p)
      (by simpa [Real.norm_eq_abs] using hsub)
    simpa [Real.norm_eq_abs] using this

  have hXle : X ≤ 3 / 2 * ((r + a : ℕ) : ℝ) ^ 2 := by
    have h := XBound.intersectionNumber_baseChange r a hN2
    simp only [hXdef] at h ⊢
    linarith [h.1, h.2]
  have hNpos : (0 : ℝ) < ((r + a : ℕ) : ℝ) := by linarith
  have hD : (0 : ℝ) < 4 * f * ((r + a : ℕ) : ℝ) ^ 2 := by positivity
  have hlog : 2 * Real.log 4 / B₀ ≤ 2.78 / (4 * f * ((r + a : ℕ) : ℝ) ^ 2) := by
    calc 2 * Real.log 4 / B₀ ≤ 2.78 / B₀ :=
          div_le_div_of_nonneg_right two_log_four_le hB0.le
      _ ≤ 2.78 / (4 * f * ((r + a : ℕ) : ℝ) ^ 2) :=
          div_le_div_of_nonneg_left (by norm_num) hD hB
  have hconst := RestConstants.intersectionNumber_baseChange.2 f (r + a) hf hN2
  have hfin : K * (2 * Real.log 4 / B₀) ≤ 1.6 * C := by
    have hl0 : 0 ≤ 2 * Real.log 4 / B₀ :=
      div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) hB0.le
    calc K * (2 * Real.log 4 / B₀)
        = (1.5 * f * X) * (2 * Real.log 4 / B₀) * C := by rw [hK]; ring
      _ ≤ (1.5 * f * (3 / 2 * ((r + a : ℕ) : ℝ) ^ 2)) * (2.78 / (4 * f * ((r + a : ℕ) : ℝ) ^ 2)) * C := by
          apply mul_le_mul_of_nonneg_right _ hC0
          apply mul_le_mul _ hlog hl0 (by positivity)
          exact mul_le_mul_of_nonneg_left hXle (by positivity)
      _ ≤ 1.6 * C := mul_le_mul_of_nonneg_right hconst hC0
  calc |∑' p : S, R p| ≤ ∑' p : S, |R p| := habs
    _ ≤ K * (2 * Real.log 4 / B₀) := htsum
    _ ≤ 1.6 * C := hfin
    _ = 1.6 * ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)| := by rw [hC]; ring
end RestBoundOfPrimeBound
end GroundTheory.Heights₂.Heights.RestTerms
