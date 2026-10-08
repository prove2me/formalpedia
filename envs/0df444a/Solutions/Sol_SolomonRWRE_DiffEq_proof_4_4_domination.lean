-- Prove2me | solution 1 for SolomonRWRE.DiffEq.proof_4_4_domination
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:53:19.502923+00:00
-- url     : https://prove2.me/submissions/f22428be-fae2-426d-8d87-12132529138e

import Mathlib
import Definitions.Def_SolomonRWRE_DiffEq_System
import Definitions.Def_SolomonRWRE_DiffEq_TwoSided

open MeasureTheory ProbabilityTheory Filter Topology


namespace SolomonRWRE.DiffEq

theorem Z_eq_sum_core {Ω : Type*} (σ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Z σ n ω = ∑ j ∈ Finset.Icc 1 n, ∏ i ∈ Finset.Icc j n, σ i ω := by
  induction n with
  | zero => simp [Z]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp only [Z, ih, Finset.Icc_self, Finset.prod_singleton, Finset.mul_sum, mul_add, mul_one]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    rw [Finset.prod_Icc_succ_top (by omega), mul_comm]


theorem domination_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (σ : ℤ → Ω → ℝ) (hσ : IsIIDNonnegZ P σ) :
    (∀ (n : ℕ) (ω : Ω), ENNReal.ofReal (Z (fun m : ℕ => σ m) n ω) ≤ S σ n ω) ∧
    (nu P (fun m : ℕ => σ m) < 1 → ∀ n : ℤ, ∀ᵐ ω ∂P, S σ n ω < ⊤) := by
  constructor
  · intro n ω
    rw [Z_eq_sum_core, ENNReal.ofReal_sum_of_nonneg
      (fun j _ => Finset.prod_nonneg fun i _ => hσ.nonneg _ ω)]
    simp_rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hσ.nonneg _ ω)]
    unfold S
    calc ∑ j ∈ Finset.Icc 1 n, ∏ i ∈ Finset.Icc j n, ENNReal.ofReal (σ i ω)
        = ∑ m ∈ Finset.range n, ∏ l ∈ Finset.range (m + 1),
            ENNReal.ofReal (σ ((n : ℤ) - l) ω) := ?_
      _ ≤ _ := ENNReal.sum_le_tsum _
    refine Finset.sum_nbij' (fun j => n - j) (fun m => n - m) ?_ ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢; omega
    · intro m hm; simp only [Finset.mem_Icc, Finset.mem_range] at hm ⊢; omega
    · intro j hj; simp only [Finset.mem_Icc, Finset.coe_Icc, Set.mem_Icc] at hj; omega
    · intro m hm; simp only [Finset.mem_range, Finset.coe_range, Set.mem_Iio] at hm; omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      refine Finset.prod_nbij' (fun i => n - i) (fun l => n - l) ?_ ?_ ?_ ?_ ?_
      · intro i hi; simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢; omega
      · intro l hl; simp only [Finset.mem_Icc, Finset.mem_range] at hl ⊢; omega
      · intro i hi; simp only [Finset.mem_Icc, Finset.coe_Icc, Set.mem_Icc] at hi; omega
      · intro l hl; simp only [Finset.mem_range, Finset.coe_range, Set.mem_Iio] at hl; omega
      · intro i hi
        simp only [Finset.mem_Icc] at hi
        congr 2
        omega
  · intro hν n
    have hmeas : ∀ m : ℤ, Measurable (fun ω => ENNReal.ofReal (σ m ω)) :=
      fun m => ENNReal.measurable_ofReal.comp (hσ.meas m)
    have hS : Measurable (S σ n) := by
      unfold S
      exact Measurable.ennreal_tsum fun m => Finset.measurable_prod _ fun l _ => hmeas _
    have hind : iIndepFun (fun l : ℕ => fun ω => ENNReal.ofReal (σ (n - l) ω)) P := by
      have h1 : iIndepFun (fun m : ℤ => fun ω => ENNReal.ofReal (σ m ω)) P :=
        hσ.indep.comp (fun _ => ENNReal.ofReal) (fun _ => ENNReal.measurable_ofReal)
      exact h1.precomp (g := fun l : ℕ => n - (l : ℤ)) (fun a b h => by simpa using h)
    have hnu1 : nu P (fun m : ℕ => σ m) = ∫⁻ ω, ENNReal.ofReal (σ 1 ω) ∂P := by simp [nu]
    have hlin : ∀ m : ℤ, ∫⁻ ω, ENNReal.ofReal (σ m ω) ∂P = nu P (fun m : ℕ => σ m) := by
      intro m; rw [hnu1]
      exact ((hσ.ident m).comp ENNReal.measurable_ofReal).lintegral_eq
    have hint : ∫⁻ ω, S σ n ω ∂P = ∑' m : ℕ, nu P (fun m : ℕ => σ m) ^ (m + 1) := by
      unfold S
      rw [lintegral_tsum (fun m => (Finset.measurable_prod _ fun l _ => hmeas _).aemeasurable)]
      congr 1; ext m
      rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _ hind (fun l => hmeas _)]
      simp [hlin]
    have hfin : ∫⁻ ω, S σ n ω ∂P ≠ ⊤ := by
      rw [hint]
      simp_rw [pow_succ]
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
      exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hν).ne') (ne_top_of_lt hν)
    exact ae_lt_top hS hfin

end SolomonRWRE.DiffEq

open SolomonRWRE.DiffEq


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (σ : ℤ → Ω → ℝ) (hσ : IsIIDNonnegZ P σ) :
    (∀ (n : ℕ) (ω : Ω), ENNReal.ofReal (Z (fun m : ℕ => σ m) n ω) ≤ S σ n ω) ∧
    (nu P (fun m : ℕ => σ m) < 1 → ∀ n : ℤ, ∀ᵐ ω ∂P, S σ n ω < ⊤) := by
  exact domination_core P σ hσ
