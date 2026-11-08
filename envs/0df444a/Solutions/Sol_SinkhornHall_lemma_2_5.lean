-- Prove2me | solution 1 for SinkhornHall.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T04:04:56.292199+00:00
-- url     : https://prove2.me/submissions/8b5aeedf-60b9-4372-85a7-594195710ca9

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis

open Finset

namespace Aux_SinkhornL25
open SinkhornHall

lemma partB {K : Type*} [Fintype K] [Nontrivial K] {d : ℕ} (q : K → ℝ)
    (hq : ∀ k, 0 < q k) (ω : K → Fin d → ℝ) (ξ : Fin d → ℝ)
    (h : gpObjective q ω ξ ≤ Real.log (Finset.univ.inf' Finset.univ_nonempty q)) :
    ∀ k, ω k ⬝ᵥ ξ < 0 := by
  classical
  intro k
  unfold gpObjective at h
  have hterm : ∀ k, 0 < q k * Real.exp (ω k ⬝ᵥ ξ) := fun k => mul_pos (hq k) (Real.exp_pos _)
  have hS : 0 < ∑ k, q k * Real.exp (ω k ⬝ᵥ ξ) :=
    Finset.sum_pos (fun k _ => hterm k) Finset.univ_nonempty
  have hm : 0 < Finset.univ.inf' Finset.univ_nonempty q := by
    rw [Finset.lt_inf'_iff]; exact fun k _ => hq k
  rw [Real.log_le_log_iff hS hm] at h
  obtain ⟨j, hj⟩ := exists_ne k
  have h2 : q k * Real.exp (ω k ⬝ᵥ ξ) + q j * Real.exp (ω j ⬝ᵥ ξ) ≤
      ∑ k, q k * Real.exp (ω k ⬝ᵥ ξ) := by
    rw [← Finset.sum_pair (f := fun k => q k * Real.exp (ω k ⬝ᵥ ξ)) (Ne.symm hj)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => (hterm i).le)
  have h3 : Finset.univ.inf' Finset.univ_nonempty q ≤ q k :=
    Finset.inf'_le _ (Finset.mem_univ k)
  have h4 : q k * Real.exp (ω k ⬝ᵥ ξ) < q k * 1 := by
    have := hterm j
    linarith
  have h5 : Real.exp (ω k ⬝ᵥ ξ) < 1 := lt_of_mul_lt_mul_left h4 (hq k).le
  exact Real.exp_lt_one_iff.mp h5

end Aux_SinkhornL25

open SinkhornHall Aux_SinkhornL25 in
theorem solution {K : Type*} [Fintype K] [Nontrivial K] {d : ℕ} (q : K → ℝ)
    (hq : ∀ k, 0 < q k) (ω : K → Fin d → ℝ) :
    ((∀ M : ℝ, ∃ ξ : Fin d → ℝ, gpObjective q ω ξ < M) ↔
        ∃ ξ : Fin d → ℝ, ∀ k, ω k ⬝ᵥ ξ < 0) ∧
      ∀ ξ : Fin d → ℝ,
        gpObjective q ω ξ ≤ Real.log (Finset.univ.inf' Finset.univ_nonempty q) →
          ∀ k, ω k ⬝ᵥ ξ < 0 := by
  refine ⟨⟨fun h => ?_, fun ⟨ξ, hξ⟩ M => ?_⟩, partB q hq ω⟩
  · obtain ⟨ξ, hξ⟩ := h (Real.log (Finset.univ.inf' Finset.univ_nonempty q))
    exact ⟨ξ, partB q hq ω ξ hξ.le⟩
  · have hlim : Filter.Tendsto (fun t : ℝ => ∑ k, q k * Real.exp (t * (ω k ⬝ᵥ ξ)))
        Filter.atTop (nhds (∑ _k : K, (0:ℝ))) := by
      apply tendsto_finsetSum
      intro k _
      have h1 : Filter.Tendsto (fun t : ℝ => t * (ω k ⬝ᵥ ξ)) Filter.atTop Filter.atBot :=
        Filter.tendsto_id.atTop_mul_const_of_neg (hξ k)
      have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul (q k)
      simpa using h2
    rw [Finset.sum_const_zero] at hlim
    obtain ⟨t, ht⟩ := (hlim.eventually (gt_mem_nhds (Real.exp_pos M))).exists
    refine ⟨t • ξ, ?_⟩
    unfold gpObjective
    have hS : 0 < ∑ k, q k * Real.exp (ω k ⬝ᵥ (t • ξ)) :=
      Finset.sum_pos (fun k _ => mul_pos (hq k) (Real.exp_pos _)) Finset.univ_nonempty
    rw [Real.log_lt_iff_lt_exp hS]
    simp only [dotProduct_smul, smul_eq_mul]
    exact ht
