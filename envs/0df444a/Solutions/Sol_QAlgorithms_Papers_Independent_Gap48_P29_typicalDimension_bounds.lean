-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P29.typicalDimension_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T20:42:16.204901+00:00
-- url     : https://prove2.me/submissions/32c0b763-6a29-4dbb-8a3f-5110afe5dfc9

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter
open scoped Matrix ComplexConjugate ComplexOrder Topology

/-- spectral data of a cfc-indicator projector of a density matrix -/
lemma X7U_spec {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Matrix ι ι ℂ)
    (hρ : IsDensityMatrix ρ) (lo hi : ℝ) :
    let hH : ρ.IsHermitian := hρ.1.1
    let W := Finset.univ.filter (fun i => lo ≤ hH.eigenvalues i ∧ hH.eigenvalues i ≤ hi)
    let P := cfc (fun x : ℝ => if lo ≤ x ∧ x ≤ hi then (1 : ℝ) else 0) ρ
    projectionDimension P = W.card ∧
      ((P * ρ * P).trace).re = ∑ i ∈ W, hH.eigenvalues i ∧
      (∀ i, 0 ≤ hH.eigenvalues i) ∧ ∑ i, hH.eigenvalues i = 1 := by
  intro hH W P
  set f : ℝ → ℝ := fun x => if lo ≤ x ∧ x ≤ hi then (1 : ℝ) else 0 with hf
  set U : Matrix ι ι ℂ := (hH.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hUU : star U * U = 1 := Matrix.UnitaryGroup.star_mul_self hH.eigenvectorUnitary
  have hUU' : U * star U = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
    exact this
  set D : Matrix ι ι ℂ := Matrix.diagonal (RCLike.ofReal ∘ f ∘ hH.eigenvalues) with hD
  set L : Matrix ι ι ℂ := Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) with hL
  have hPe : P = U * D * star U := by
    show cfc f ρ = _
    rw [hH.cfc_eq f]
    rfl
  have hρe : ρ = U * L * star U := by
    conv_lhs => rw [hH.spectral_theorem]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold projectionDimension
    rw [Matrix.toEuclideanLin_eq_toLin, ← Matrix.rank_eq_finrank_range_toLin]
    rw [hPe, Matrix.rank_mul_eq_left_of_isUnit_det _ _
        (Matrix.isUnit_det_of_left_inverse hUU'),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnit_det_of_left_inverse hUU),
      Matrix.rank_diagonal, Fintype.card_subtype]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply, hf, W]
    split_ifs with h <;> simp [h]
  · have hprod : P * ρ * P = U * (D * L * D) * star U := by
      rw [hPe, hρe]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul, ← Matrix.mul_assoc (star U) U, hUU,
        Matrix.one_mul]
    rw [hprod, Matrix.trace_mul_cycle, hUU, Matrix.one_mul]
    simp only [hD, hL, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Function.comp_apply]
    rw [Complex.re_sum]
    simp only [W, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hf]
    split_ifs <;> simp
  · intro i
    exact hρ.1.eigenvalues_nonneg i
  · have h := hH.trace_eq_sum_eigenvalues
    rw [hρ.2] at h
    have h2 := congrArg Complex.re h
    simp only [Complex.one_re, Complex.re_sum] at h2
    rw [h2]
    simp

end QAlgorithms.Papers.Independent.Gap48.P29

end

noncomputable section

open QAlgorithms Filter
open scoped Matrix ComplexConjugate ComplexOrder Topology
open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)
open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Gap48.P29 in
theorem solution (S : BlockQuantumSource) (hS : QAEP S)
    (window delta : ℝ) (hwindow : 0 < window) (hdelta : 0 < delta)
    (n : ℕ) (hn : 0 < n) (hmass : 1 - delta < qaepRetainedMass S window n) :
    (1 - delta) * (2 : ℝ) ^ ((n : ℝ) * (sourceEntropyRate S - window)) ≤
      (projectionDimension (qaepSpectralProjector S window n) : ℝ) ∧
    (projectionDimension (qaepSpectralProjector S window n) : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) * (sourceEntropyRate S + window)) := by
  set R := sourceEntropyRate S
  set x : ℝ := (2 : ℝ) ^ ((n : ℝ) * (R + window)) with hx
  set y : ℝ := (2 : ℝ) ^ ((n : ℝ) * (R - window)) with hy
  have hxpos : 0 < x := Real.rpow_pos_of_pos (by norm_num) _
  have hypos : 0 < y := Real.rpow_pos_of_pos (by norm_num) _
  have hlo : (2 : ℝ) ^ (-(n : ℝ) * (R + window)) = x⁻¹ := by
    rw [neg_mul, Real.rpow_neg (by norm_num)]
  have hhi : (2 : ℝ) ^ (-(n : ℝ) * (R - window)) = y⁻¹ := by
    rw [neg_mul, Real.rpow_neg (by norm_num)]
  obtain ⟨hdim, hm, hnn, hsum⟩ := X7U_spec (S.rho n) (S.density n)
    ((2 : ℝ) ^ (-(n : ℝ) * (R + window))) ((2 : ℝ) ^ (-(n : ℝ) * (R - window)))
  have hP : qaepSpectralProjector S window n = cfc (fun x : ℝ =>
      if (2 : ℝ) ^ (-(n : ℝ) * (R + window)) ≤ x ∧ x ≤ (2 : ℝ) ^ (-(n : ℝ) * (R - window))
      then (1 : ℝ) else 0) (S.rho n) := rfl
  have hM : qaepRetainedMass S window n = ((qaepSpectralProjector S window n * S.rho n *
      qaepSpectralProjector S window n).trace).re := rfl
  rw [hM, hP, hm] at hmass
  rw [hP, hdim]
  rw [hlo, hhi] at hmass ⊢
  set H := (S.density n).1.1
  set W := Finset.univ.filter (fun i => x⁻¹ ≤ H.eigenvalues i ∧ H.eigenvalues i ≤ y⁻¹)
  have h1 : W.card • x⁻¹ ≤ ∑ i ∈ W, H.eigenvalues i :=
    Finset.card_nsmul_le_sum W _ _ (fun i hi => (Finset.mem_filter.1 hi).2.1)
  have h2 : ∑ i ∈ W, H.eigenvalues i ≤ W.card • y⁻¹ :=
    Finset.sum_le_card_nsmul W _ _ (fun i hi => (Finset.mem_filter.1 hi).2.2)
  have h3 : ∑ i ∈ W, H.eigenvalues i ≤ 1 := by
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => hnn i)
  rw [nsmul_eq_mul] at h1 h2
  constructor
  · have : 1 - delta < (W.card : ℝ) * y⁻¹ := lt_of_lt_of_le hmass h2
    have h4 : (1 - delta) * y < W.card := by
      have := mul_lt_mul_of_pos_right this hypos
      rwa [mul_assoc, inv_mul_cancel₀ hypos.ne', mul_one] at this
    exact h4.le
  · have h5 : (W.card : ℝ) * x⁻¹ ≤ 1 := le_trans h1 h3
    have := mul_le_mul_of_nonneg_right h5 hxpos.le
    rwa [mul_assoc, inv_mul_cancel₀ hxpos.ne', mul_one, one_mul] at this

end
