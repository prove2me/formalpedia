-- Prove2me | solution 1 for RegevLWE.Hyperplane.lemma_3_15
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:27:05.331273+00:00
-- url     : https://prove2.me/submissions/e7280e4e-78ab-4b7c-bc12-a665e387f040

import Mathlib
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian
import Theorems.Thm_RegevLWE_Hyperplane_expectation_lt_nine_tenths
import Theorems.Thm_RegevLWE_Hyperplane_rhoLattice_poisson

open RegevLWE.Hyperplane

theorem solution {n : ℕ} (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] {ε r : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10)
    (hr : 0 < r) (h : Real.sqrt 2 * RegevLWE.GaussConv.smoothingParam L ε ≤ r)
    (H : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hH : Module.finrank ℝ H ≤ n - 1) :
    (1 / 10 : ℝ) ≤
      ∑' x : {x : L // (x : EuclideanSpace ℝ (Fin n)) ∉ H}, discreteGaussian L r x := by
  have h_finrank_tot : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n :=
    finrank_euclideanSpace_fin
  have h_orth_sum :
      Module.finrank ℝ H + Module.finrank ℝ Hᗮ =
        Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) :=
    H.finrank_add_finrank_orthogonal
  have h_exists_v : ∃ v : Hᗮ, v ≠ 0 := by
    by_contra h_all
    push_neg at h_all
    haveI : Subsingleton Hᗮ := Subsingleton.intro (fun a b => by rw [h_all a, h_all b])
    have h0 : Module.finrank ℝ Hᗮ = 0 := Module.finrank_zero_of_subsingleton
    omega
  rcases h_exists_v with ⟨v, hv⟩
  have hv_coe : (v : EuclideanSpace ℝ (Fin n)) ≠ 0 := Submodule.coe_eq_zero.not.mpr hv
  have hv_norm : ‖(v : EuclideanSpace ℝ (Fin n))‖ ≠ 0 := norm_ne_zero_iff.mpr hv_coe
  let w : EuclideanSpace ℝ (Fin n) :=
    ‖(v : EuclideanSpace ℝ (Fin n))‖⁻¹ • (v : EuclideanSpace ℝ (Fin n))
  have hw : ‖w‖ = 1 := by
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hv_norm]
  have hw_mem : w ∈ Hᗮ := Hᗮ.smul_mem ‖(v : EuclideanSpace ℝ (Fin n))‖⁻¹ v.2
  have hw_orth : ∀ u ∈ H, inner ℝ w u = 0 := by
    intro u hu
    rw [real_inner_comm]
    exact (H.mem_orthogonal w).mp hw_mem u hu
  have h_exp_bound := expectation_lt_nine_tenths L hε hε10 hr h w hw
  have h_exp_lt :
      (∑' x : L, discreteGaussian L r x *
          Real.exp (-Real.pi * (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2 / r ^ 2)) <
        9 / 10 :=
    lt_of_le_of_lt h_exp_bound.1 h_exp_bound.2
  have h_poiss := (rhoLattice_poisson L hr).2
  have h_cov_pos : 0 < ZLattice.covolume L := ZLattice.covolume_pos L
  have h_rho_pos : 0 < rhoLattice r L :=
    lt_of_lt_of_le (mul_pos (inv_pos.mpr h_cov_pos) (pow_pos hr n)) h_poiss
  have h_summable_rho :
      Summable (fun x : L => RegevLWE.GaussConv.rho r (x : EuclideanSpace ℝ (Fin n))) := by
    by_contra h_not
    have h_zero : rhoLattice r L = 0 := tsum_eq_zero_of_not_summable h_not
    linarith
  have h_summable_dg : Summable (discreteGaussian L r) :=
    h_summable_rho.div_const (rhoLattice r L)
  have h_dg_nonneg : ∀ x : L, 0 ≤ discreteGaussian L r x := by
    intro x
    unfold discreteGaussian RegevLWE.GaussConv.rho
    exact div_nonneg (Real.exp_nonneg _) (le_of_lt h_rho_pos)
  let f : L → ℝ := fun x =>
    discreteGaussian L r x *
      Real.exp (-Real.pi * (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2 / r ^ 2)
  have hf_nonneg : ∀ x : L, 0 ≤ f x := by
    intro x
    exact mul_nonneg (h_dg_nonneg x) (Real.exp_nonneg _)
  have hf_le : ∀ x : L, f x ≤ discreteGaussian L r x := by
    intro x
    dsimp [f]
    have h_arg_nonpos :
        -Real.pi * (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2 / r ^ 2 ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · have : 0 ≤ Real.pi * (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2 :=
          mul_nonneg Real.pi_nonneg (sq_nonneg _)
        linarith
      · exact sq_nonneg r
    exact mul_le_of_le_one_right (h_dg_nonneg x) (Real.exp_le_one_iff.mpr h_arg_nonpos)
  have h_summable_f : Summable f := Summable.of_nonneg_of_le hf_nonneg hf_le h_summable_dg
  let S : Set L := {x : L | (x : EuclideanSpace ℝ (Fin n)) ∈ H}
  have h_split_dg := h_summable_dg.tsum_subtype_add_tsum_subtype_compl S
  change (∑' x : {x : L // (x : EuclideanSpace ℝ (Fin n)) ∈ H}, discreteGaussian L r x) +
      (∑' x : {x : L // (x : EuclideanSpace ℝ (Fin n)) ∉ H}, discreteGaussian L r x) =
    ∑' x : L, discreteGaussian L r x at h_split_dg
  have h_total_dg : (∑' x : L, discreteGaussian L r x) = 1 := by
    unfold discreteGaussian
    rw [tsum_div_const]
    exact div_self (ne_of_gt h_rho_pos)
  have h_in_H_eq :
      (∑' x : {x : L // (x : EuclideanSpace ℝ (Fin n)) ∈ H}, discreteGaussian L r x) =
        ∑' x : {x : L // (x : EuclideanSpace ℝ (Fin n)) ∈ H}, f x := by
    congr 1
    ext x
    dsimp [f]
    rw [hw_orth (x.1 : EuclideanSpace ℝ (Fin n)) x.2]
    simp
  have h_split_f := h_summable_f.tsum_subtype_add_tsum_subtype_compl S
  change (∑' x : {x : L // (x : EuclideanSpace ℝ (Fin n)) ∈ H}, f x) +
      (∑' x : {x : L // (x : EuclideanSpace ℝ (Fin n)) ∉ H}, f x) =
    ∑' x : L, f x at h_split_f
  have h_compl_f_nonneg :
      0 ≤ ∑' x : {x : L // (x : EuclideanSpace ℝ (Fin n)) ∉ H}, f x :=
    tsum_nonneg (fun x => hf_nonneg x.1)
  have h_in_H_le :
      (∑' x : {x : L // (x : EuclideanSpace ℝ (Fin n)) ∈ H}, discreteGaussian L r x) ≤
        ∑' x : L, f x := by
    linarith
  linarith
