-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P23.alphaNearOne
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T18:58:30.701993+00:00
-- url     : https://prove2.me/submissions/ecc31b9a-df03-4a13-9a7f-781fd99e0701

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23
import Mathlib

section X5mod_OL_Base
open Matrix
open scoped ComplexOrder

namespace X5OL

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- overlap matrix of the two eigenbases -/
noncomputable def ov {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) : Matrix I I ℂ :=
  star (hR.eigenvectorUnitary : Matrix I I ℂ) * (hN.eigenvectorUnitary : Matrix I I ℂ)

noncomputable def w {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i j : I) : ℝ :=
  ‖ov hR hN i j‖ ^ 2

lemma ov_unitary {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) :
    ov hR hN * star (ov hR hN) = 1 := by
  unfold ov
  have hU : star (hR.eigenvectorUnitary : Matrix I I ℂ) * (hR.eigenvectorUnitary : Matrix I I ℂ) = 1 :=
    Unitary.star_mul_self_of_mem (hR.eigenvectorUnitary).2
  have hV : (hN.eigenvectorUnitary : Matrix I I ℂ) * star (hN.eigenvectorUnitary : Matrix I I ℂ) = 1 :=
    Unitary.mul_star_self_of_mem (hN.eigenvectorUnitary).2
  rw [star_mul, star_star, Matrix.mul_assoc, ← Matrix.mul_assoc (hN.eigenvectorUnitary : Matrix I I ℂ),
    hV, Matrix.one_mul, hU]

lemma w_row {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i : I) :
    ∑ j, w hR hN i j = 1 := by
  have h := congrFun (congrFun (ov_unitary hR hN) i) i
  rw [mul_apply, one_apply_eq] at h
  have : (∑ j, ((w hR hN i j : ℝ) : ℂ)) = 1 := by
    rw [← h]; refine Finset.sum_congr rfl fun j _ => ?_
    simp only [w, star_apply, Complex.ofReal_pow]
    rw [RCLike.star_def, Complex.mul_conj']
  exact_mod_cast this

lemma w_nonneg {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i j : I) :
    0 ≤ w hR hN i j := by unfold w; positivity

lemma tr_cfc_cfc {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (f g : ℝ → ℝ) :
    (cfc f R * cfc g N).trace =
      ∑ i, ∑ j, ((f (hR.eigenvalues i) * g (hN.eigenvalues j) * w hR hN i j : ℝ) : ℂ) := by
  rw [hR.cfc_eq, hN.cfc_eq]
  unfold IsHermitian.cfc
  simp only [Unitary.conjStarAlgAut_apply]
  set U := (hR.eigenvectorUnitary : Matrix I I ℂ)
  set V := (hN.eigenvectorUnitary : Matrix I I ℂ)
  set Df := diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ f ∘ hR.eigenvalues)
  set Dg := diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ g ∘ hN.eigenvalues)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem (hR.eigenvectorUnitary).2
  have hU' : U * star U = 1 := Unitary.mul_star_self_of_mem (hR.eigenvectorUnitary).2
  have : (U * Df * star U * (V * Dg * star V)).trace = (Df * (star U * V) * Dg * star (star U * V)).trace := by
    rw [star_mul, star_star]
    rw [show U * Df * star U * (V * Dg * star V) = U * (Df * (star U * V) * Dg * (star V * U)) * star U by
      simp only [Matrix.mul_assoc]; rw [hU']; simp]
    rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  rw [this]
  change (Df * ov hR hN * Dg * star (ov hR hN)).trace = _
  have hE : ∀ i k, (Df * ov hR hN * Dg) i k =
      ((f (hR.eigenvalues i) : ℝ) : ℂ) * ov hR hN i k * ((g (hN.eigenvalues k) : ℝ) : ℂ) := by
    intro i k; simp [Df, Dg, diagonal_mul, mul_diagonal]
  simp only [Matrix.trace, diag_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hE, star_apply]
  simp only [w, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [← Complex.mul_conj', RCLike.star_def]
  ring

lemma ov_apply {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian) (i j : I) :
    ov hR hN i j = star (hR.eigenvectorBasis i).ofLp ⬝ᵥ (hN.eigenvectorBasis j).ofLp := by
  simp only [ov, mul_apply, star_apply, IsHermitian.eigenvectorUnitary_apply, dotProduct, Pi.star_apply]

lemma supp_fwd {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian)
    (h : LinearMap.ker N.mulVecLin ≤ LinearMap.ker R.mulVecLin) (i j : I)
    (hi : hR.eigenvalues i ≠ 0) (hj : hN.eigenvalues j = 0) : ov hR hN i j = 0 := by
  set b := (hR.eigenvectorBasis i).ofLp
  set v := (hN.eigenvectorBasis j).ofLp
  have hNv : N *ᵥ v = 0 := by rw [hN.mulVec_eigenvectorBasis j, hj, zero_smul]
  have hRv : R *ᵥ v = 0 := by
    have := h (show v ∈ LinearMap.ker N.mulVecLin by rw [LinearMap.mem_ker, mulVecLin_apply]; exact hNv)
    rwa [LinearMap.mem_ker, mulVecLin_apply] at this
  have key : ((hR.eigenvalues i : ℝ) : ℂ) * (star b ⬝ᵥ v) = 0 := by
    have hb : R *ᵥ b = hR.eigenvalues i • b := hR.mulVec_eigenvectorBasis i
    have : star (R *ᵥ b) ⬝ᵥ v = star b ⬝ᵥ (R *ᵥ v) := by
      rw [star_mulVec, hR.eq, dotProduct_mulVec]
    rw [hRv, dotProduct_zero, hb, star_smul] at this
    rw [← this, smul_dotProduct]
    simp [RCLike.real_smul_eq_coe_mul]
  rw [ov_apply]
  rcases mul_eq_zero.1 key with h1 | h1
  · exact absurd (by exact_mod_cast h1) hi
  · exact h1

lemma spec_mulVec {R : Matrix I I ℂ} (hR : R.IsHermitian) (x : I → ℂ) :
    R *ᵥ x = (hR.eigenvectorUnitary : Matrix I I ℂ) *ᵥ
      (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hR.eigenvalues) *ᵥ (star (hR.eigenvectorUnitary : Matrix I I ℂ) *ᵥ x)) := by
  conv_lhs => rw [hR.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, ← mulVec_mulVec, ← mulVec_mulVec]

lemma supp_bwd {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian)
    (h : ∀ i j, hR.eigenvalues i ≠ 0 → hN.eigenvalues j = 0 → ov hR hN i j = 0) :
    LinearMap.ker N.mulVecLin ≤ LinearMap.ker R.mulVecLin := by
  intro x hx
  rw [LinearMap.mem_ker, mulVecLin_apply] at hx ⊢
  set U := (hR.eigenvectorUnitary : Matrix I I ℂ)
  set V := (hN.eigenvectorUnitary : Matrix I I ℂ)
  have hV : V * star V = 1 := Unitary.mul_star_self_of_mem (hN.eigenvectorUnitary).2
  have hV' : star V * V = 1 := Unitary.star_mul_self_of_mem (hN.eigenvectorUnitary).2
  set c := star V *ᵥ x
  have hc : ∀ j, hN.eigenvalues j ≠ 0 → c j = 0 := by
    intro j hj
    have h1 : star V *ᵥ (N *ᵥ x) = 0 := by rw [hx, mulVec_zero]
    rw [spec_mulVec hN, mulVec_mulVec, hV', one_mulVec] at h1
    have := congrFun h1 j
    rw [mulVec_diagonal] at this
    simp only [Function.comp_apply, Pi.zero_apply] at this
    rcases mul_eq_zero.1 this with h2 | h2
    · exact absurd (by simpa using h2) hj
    · exact h2
  have hUx : star U *ᵥ x = ov hR hN *ᵥ c := by
    rw [show ov hR hN = star U * V from rfl, mulVec_mulVec, Matrix.mul_assoc, hV, Matrix.mul_one]
  have hD : diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hR.eigenvalues) *ᵥ (star U *ᵥ x) = 0 := by
    ext i
    rw [hUx, mulVec_diagonal, Pi.zero_apply]
    by_cases hi : hR.eigenvalues i = 0
    · simp [hi]
    · simp only [mulVec, dotProduct]
      rw [Finset.sum_eq_zero, mul_zero]
      intro j _
      by_cases hj : hN.eigenvalues j = 0
      · rw [h i j hi hj, zero_mul]
      · rw [hc j hj, mul_zero]
  rw [spec_mulVec hR, hD, mulVec_zero]

end X5OL
end X5mod_OL_Base

section X5mod_OL_Main
open Matrix Filter
open scoped ComplexOrder Topology

namespace X5OL

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- the scalar function behind tr(ρ^α N^{1-α}) -/
noncomputable def Φ (ν μ : I → ℝ) (W : I → I → ℝ) (α : ℝ) : ℝ :=
  ∑ i, ∑ j, if 0 < ν i ∧ 0 < μ j then W i j * Real.exp (α * Real.log (ν i) + (1 - α) * Real.log (μ j)) else 0

noncomputable def Φ' (ν μ : I → ℝ) (W : I → I → ℝ) : ℝ :=
  ∑ i, ∑ j, if 0 < ν i ∧ 0 < μ j then W i j * ν i * (Real.log (ν i) - Real.log (μ j)) else 0

lemma Φ_deriv (ν μ : I → ℝ) (W : I → I → ℝ) : HasDerivAt (Φ ν μ W) (Φ' ν μ W) 1 := by
  unfold Φ Φ'
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
  split_ifs with h
  · have h1 : HasDerivAt (fun α : ℝ => α * Real.log (ν i) + (1 - α) * Real.log (μ j))
        (Real.log (ν i) - Real.log (μ j)) 1 := by
      have := ((hasDerivAt_id (1 : ℝ)).mul_const (Real.log (ν i))).add
        (((hasDerivAt_const (1 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (1 : ℝ))).mul_const (Real.log (μ j)))
      exact this.congr_deriv (by ring)
    have h2 := (h1.exp).const_mul (W i j)
    refine h2.congr_deriv ?_
    simp only [one_mul, sub_self, zero_mul, add_zero, Real.exp_log h.1]
    ring
  · exact hasDerivAt_const _ _

lemma Φ_cont (ν μ : I → ℝ) (W : I → I → ℝ) : Continuous (Φ ν μ W) := by
  unfold Φ
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  split_ifs
  · fun_prop
  · exact continuous_const

lemma Φ_one (ν μ : I → ℝ) (W : I → I → ℝ) :
    Φ ν μ W 1 = ∑ i, ∑ j, if 0 < ν i ∧ 0 < μ j then W i j * ν i else 0 := by
  unfold Φ
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · simp [Real.exp_log h.1]
  · rfl

lemma tr_alpha {R N : Matrix I I ℂ} (hR : R.IsHermitian) (hN : N.IsHermitian)
    (hR0 : ∀ i, 0 ≤ hR.eigenvalues i) (hN0 : ∀ j, 0 ≤ hN.eigenvalues j) (α : ℝ) (hα : 0 < α) :
    (cfc (fun x : ℝ => x ^ α) R * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - α)) N).trace.re =
      Φ hR.eigenvalues hN.eigenvalues (w hR hN) α := by
  rw [tr_cfc_cfc hR hN, Complex.re_sum]
  unfold Φ
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.ofReal_re]
  rcases (hR0 i).lt_or_eq with hi | hi
  · rcases (hN0 j).lt_or_eq with hj | hj
    · rw [if_neg hj.ne', if_pos ⟨hi, hj⟩, Real.rpow_def_of_pos hi, Real.rpow_def_of_pos hj, ← Real.exp_add]
      ring_nf
    · rw [← hj]; simp
  · rw [← hi]; simp [Real.zero_rpow hα.ne']

section scalar
variable (ν μ : I → ℝ) (W : I → I → ℝ) (hν : ∀ i, 0 ≤ ν i) (hμ : ∀ j, 0 ≤ μ j)
  (hW : ∀ i j, 0 ≤ W i j) (hrow : ∀ i, ∑ j, W i j = 1)
include hν hμ hrow

lemma Φ_one_supp (hs : ∀ i j, ν i ≠ 0 → μ j = 0 → W i j = 0) : Φ ν μ W 1 = ∑ i, ν i := by
  rw [Φ_one]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (Finset.sum_congr rfl fun j _ => ?_).trans
    (show ∑ j, ν i * W i j = ν i by rw [← Finset.mul_sum, hrow, mul_one])
  rcases (hν i).lt_or_eq with hi | hi
  · rcases (hμ j).lt_or_eq with hj | hj
    · rw [if_pos ⟨hi, hj⟩]; ring
    · rw [if_neg (fun h => h.2.ne hj), hs i j hi.ne' hj.symm, mul_zero]
  · rw [if_neg (fun h => h.1.ne hi), ← hi, zero_mul]

lemma value_supp (hs : ∀ i j, ν i ≠ 0 → μ j = 0 → W i j = 0) :
    (∑ i, ∑ j, ν i * Real.logb 2 (μ j) * W i j) + -∑ i, ν i * Real.logb 2 (ν i) =
      -Φ' ν μ W / Real.log 2 := by
  unfold Φ'
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show ν i * Real.logb 2 (ν i) = ∑ j, ν i * Real.logb 2 (ν i) * W i j by
      rw [← Finset.mul_sum, hrow, mul_one]]
  rw [Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases (hν i).lt_or_eq with hi | hi
  · rcases (hμ j).lt_or_eq with hj | hj
    · rw [if_pos ⟨hi, hj⟩]; unfold Real.logb; ring
    · rw [if_neg (fun h => h.2.ne hj), hs i j hi.ne' hj.symm]; simp
  · rw [if_neg (fun h => h.1.ne hi), ← hi]; simp

include hW in
lemma Φ_one_lt (hex : ∃ i j, ν i ≠ 0 ∧ μ j = 0 ∧ W i j ≠ 0) : Φ ν μ W 1 < ∑ i, ν i := by
  obtain ⟨i0, j0, hi0, hj0, hw0⟩ := hex
  rw [Φ_one]
  have hle : ∀ i j, (if 0 < ν i ∧ 0 < μ j then W i j * ν i else 0) ≤ W i j * ν i := by
    intro i j; split_ifs
    · exact le_rfl
    · exact mul_nonneg (hW i j) (hν i)
  refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i0, Finset.mem_univ _, ?_⟩
  · calc _ ≤ ∑ j, W i j * ν i := Finset.sum_le_sum fun j _ => hle i j
      _ = ν i := by rw [← Finset.sum_mul, hrow, one_mul]
  · calc _ < ∑ j, W i0 j * ν i0 := by
          refine Finset.sum_lt_sum (fun j _ => hle i0 j) ⟨j0, Finset.mem_univ _, ?_⟩
          rw [if_neg (fun h => h.2.ne' hj0)]
          exact mul_pos ((hW i0 j0).lt_of_ne (Ne.symm hw0)) ((hν i0).lt_of_ne (Ne.symm hi0))
      _ = ν i0 := by rw [← Finset.sum_mul, hrow, one_mul]

omit hrow in
include hW in
lemma Φ_zero (h0 : Φ ν μ W 1 = 0) (α : ℝ) : Φ ν μ W α = 0 := by
  rw [Φ_one] at h0
  have hnn : ∀ i j, 0 ≤ (if 0 < ν i ∧ 0 < μ j then W i j * ν i else 0) := by
    intro i j; split_ifs
    · exact mul_nonneg (hW i j) (hν i)
    · exact le_rfl
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => hnn i j)).1 h0
  unfold Φ
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn i j)).1 (h1 i (Finset.mem_univ _)) j
    (Finset.mem_univ _)
  split_ifs at h2 ⊢ with h
  · rcases mul_eq_zero.1 h2 with h3 | h3
    · rw [h3, zero_mul]
    · exact absurd h3 h.1.ne'
  · rfl

end scalar

end X5OL
end X5mod_OL_Main

section X5mod_OL_Thm
open Matrix Filter Set
open scoped ComplexOrder Topology

namespace X5OL
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

lemma N_psd (sigma : Matrix B B ℂ) (hs : sigma.PosSemidef) :
    (identityTensorReference (A := A) sigma).PosSemidef := by
  unfold identityTensorReference Matrix.kronecker
  exact Matrix.PosSemidef.kronecker Matrix.PosSemidef.one hs

/-- real limit in the supported case -/
lemma real_limit {I : Type*} [Fintype I] [DecidableEq I] (ν μ : I → ℝ) (W : I → I → ℝ) (h1 : Φ ν μ W 1 = 1) :
    Tendsto (fun t => 1 / (1 - t) * Real.logb 2 (Φ ν μ W t)) (𝓝[{t : ℝ | 0 < t ∧ t ≠ 1}] 1)
      (𝓝 (-Φ' ν μ W / Real.log 2)) := by
  set ψ := fun t => Real.log (Φ ν μ W t) / Real.log 2
  have hψ : HasDerivAt ψ (Φ' ν μ W / Φ ν μ W 1 / Real.log 2) 1 :=
    ((Φ_deriv ν μ W).log (by rw [h1]; norm_num)).div_const _
  rw [h1, div_one] at hψ
  have hs := (hasDerivAt_iff_tendsto_slope.1 hψ).neg
  have hmono : 𝓝[{t : ℝ | 0 < t ∧ t ≠ 1}] (1 : ℝ) ≤ 𝓝[{(1 : ℝ)}ᶜ] 1 :=
    nhdsWithin_mono _ fun t ht => ht.2
  rw [neg_div]
  refine (hs.mono_left hmono).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht1 : t - 1 ≠ 0 := sub_ne_zero.2 ht.2
  have hψ1 : ψ 1 = 0 := by simp [ψ, h1]
  rw [slope_def_field, hψ1, sub_zero]
  simp only [ψ, Real.logb]
  field_simp
  have : (1 - t) = -(t - 1) := by ring
  rw [this]; field_simp

lemma real_atBot {I : Type*} [Fintype I] [DecidableEq I] (ν μ : I → ℝ) (W : I → I → ℝ)
    (h0 : 0 < Φ ν μ W 1) (h1 : Φ ν μ W 1 < 1) :
    Tendsto (fun t => 1 / (1 - t) * Real.logb 2 (Φ ν μ W t)) (𝓝[Ioo 0 1] 1) atBot := by
  have hC : Real.logb 2 (Φ ν μ W 1) < 0 := Real.logb_neg (by norm_num) h0 h1
  have hg : Tendsto (fun t => Real.logb 2 (Φ ν μ W t)) (𝓝[Ioo 0 1] 1) (𝓝 (Real.logb 2 (Φ ν μ W 1))) := by
    have : ContinuousAt (fun t => Real.log (Φ ν μ W t) / Real.log 2) 1 :=
      ((Φ_cont ν μ W).continuousAt.log h0.ne').div_const _
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have hsub : Tendsto (fun t : ℝ => 1 - t) (𝓝[Ioo 0 1] 1) (𝓝[Ioi 0] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 (1 - 1)) := (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_pos.2 ht.2
  have hf : Tendsto (fun t : ℝ => 1 / (1 - t)) (𝓝[Ioo 0 1] 1) atTop := by
    simp only [one_div]
    exact tendsto_inv_nhdsGT_zero.comp hsub
  exact hf.atTop_mul_neg hC hg

theorem main [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    Tendsto (finiteAlpha rho sigma)
      (nhdsWithin 1 {t : ℝ | 0 < t ∧ t ≠ 1}) (nhds (fixedVonNeumann rho sigma)) ∧
      alphaEntropy rho sigma 1 = fixedVonNeumann rho sigma := by
  refine ⟨?_, by simp [alphaEntropy, finiteAlpha]⟩
  set N := identityTensorReference (A := A) sigma with hNdef
  have hNpsd : N.PosSemidef := N_psd sigma hsigma.1
  have hR := hrho.1.isHermitian
  have hN := hNpsd.isHermitian
  set ν := hR.eigenvalues
  set μ := hN.eigenvalues
  set W := w hR hN
  have hν : ∀ i, 0 ≤ ν i := hrho.1.eigenvalues_nonneg
  have hμ : ∀ j, 0 ≤ μ j := hNpsd.eigenvalues_nonneg
  have hW : ∀ i j, 0 ≤ W i j := w_nonneg hR hN
  have hrow : ∀ i, ∑ j, W i j = 1 := w_row hR hN
  -- traces as sums
  have hcfc1 : cfc (fun _ : ℝ => (1 : ℝ)) N = 1 := cfc_const_one ℝ N hN.isSelfAdjoint
  have hsingle : ∀ f : ℝ → ℝ, (cfc f rho).trace.re = ∑ i, f (ν i) := by
    intro f
    have := tr_cfc_cfc hR hN f (fun _ => 1)
    rw [hcfc1, Matrix.mul_one] at this
    rw [this, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    simp only [Complex.ofReal_re, mul_one]
    rw [← Finset.mul_sum, hrow, mul_one]
  have htr : ∑ i, ν i = 1 := by
    have := hsingle (fun x => x)
    rw [cfc_id' ℝ rho hR.isSelfAdjoint, hrho.2] at this
    simpa using this.symm
  have hF : ∀ t : ℝ, 0 < t →
      (cfc (fun x : ℝ => x ^ t) rho * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) N).trace.re =
        Φ ν μ W t := fun t ht => tr_alpha hR hN hν hμ t ht
  have hFA : ∀ t : ℝ, 0 < t → t ≠ 1 → finiteAlpha rho sigma t =
      if 1 < t ∧ ¬ supportedBy rho N then ⊥
      else (((1 / (1 - t) : ℝ)) : EReal) * log2Extended (Φ ν μ W t) := by
    intro t ht ht1
    unfold finiteAlpha
    rw [if_neg ht1, hF t ht]
  by_cases hS : supportedBy rho N
  · -- supported case
    have hs : ∀ i j, ν i ≠ 0 → μ j = 0 → W i j = 0 := by
      intro i j hi hj
      simp only [W, w, supp_fwd hR hN hS i j hi hj, norm_zero]; norm_num
    have hΦ1 : Φ ν μ W 1 = 1 := by rw [Φ_one_supp ν μ W hν hμ hrow hs, htr]
    have hval : fixedVonNeumann rho sigma = ((-Φ' ν μ W / Real.log 2 : ℝ) : EReal) := by
      unfold fixedVonNeumann
      rw [if_pos hS, ← value_supp ν μ W hν hμ hrow hs]
      congr 2
      · have := tr_cfc_cfc hR hN (fun x => x) (fun x => Real.logb 2 x)
        rw [cfc_id' ℝ rho hR.isSelfAdjoint] at this
        rw [this, Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.re_sum]; simp only [Complex.ofReal_re]; rfl
      · unfold QAlgorithms.vnEntropy
        rw [hsingle]
    rw [hval]
    have hpos : ∀ᶠ t in 𝓝 (1 : ℝ), 0 < Φ ν μ W t :=
      (Φ_cont ν μ W).continuousAt.eventually (lt_mem_nhds (by rw [hΦ1]; norm_num))
    refine (EReal.tendsto_coe.2 (real_limit ν μ W hΦ1)).congr' ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hpos] with t ht hp
    rw [hFA t ht.1 ht.2, if_neg (fun h => h.2 hS)]
    unfold log2Extended
    rw [if_neg hp.ne', ← EReal.coe_mul]
  · -- unsupported case
    have hex : ∃ i j, ν i ≠ 0 ∧ μ j = 0 ∧ W i j ≠ 0 := by
      by_contra hne
      push Not at hne
      apply hS
      refine supp_bwd hR hN fun i j hi hj => ?_
      have := hne i j hi hj
      simp only [W, w] at this
      exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
    have hlt : Φ ν μ W 1 < 1 := htr ▸ Φ_one_lt ν μ W hν hμ hW hrow hex
    have hval : fixedVonNeumann rho sigma = ⊥ := by unfold fixedVonNeumann; rw [if_neg hS]
    rw [hval]
    have hset : {t : ℝ | 0 < t ∧ t ≠ 1} = Ioo 0 1 ∪ Ioi 1 := by
      ext t; simp only [mem_ofPred_eq, mem_union, mem_Ioo, mem_Ioi]
      constructor
      · rintro ⟨h0, h1⟩
        rcases lt_or_gt_of_ne h1 with h | h
        · exact Or.inl ⟨h0, h⟩
        · exact Or.inr h
      · rintro (⟨h0, h1⟩ | h)
        · exact ⟨h0, h1.ne⟩
        · exact ⟨by linarith, h.ne'⟩
    rw [hset, nhdsWithin_union]
    refine Tendsto.sup ?_ ?_
    · -- left
      have hΦnn : 0 ≤ Φ ν μ W 1 := by
        rw [Φ_one]
        exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
          split_ifs
          · exact mul_nonneg (hW i j) (hν i)
          · exact le_rfl
      rcases hΦnn.eq_or_lt with h0 | h0
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        rw [hFA t ht.1 ht.2.ne, if_neg (fun h => absurd h.1 (not_lt.2 ht.2.le)),
          Φ_zero ν μ W hν hμ hW h0.symm t]
        unfold log2Extended
        rw [if_pos rfl, EReal.coe_mul_bot_of_pos (by have := ht.2; rw [one_div]; exact inv_pos.2 (by linarith))]
      · rw [EReal.tendsto_nhds_bot_iff_real]
        intro x
        have hpos : ∀ᶠ t in 𝓝 (1 : ℝ), 0 < Φ ν μ W t :=
          (Φ_cont ν μ W).continuousAt.eventually (lt_mem_nhds h0)
        filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hpos,
          (real_atBot ν μ W h0 hlt).eventually (eventually_lt_atBot x)] with t ht hp hlx
        rw [hFA t ht.1 ht.2.ne, if_neg (fun h => absurd h.1 (not_lt.2 ht.2.le))]
        unfold log2Extended
        rw [if_neg hp.ne', ← EReal.coe_mul, EReal.coe_lt_coe_iff]
        exact hlx
    · -- right
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [hFA t (by have := ht; simp only [mem_Ioi] at this; linarith) (ne_of_gt ht), if_pos ⟨ht, hS⟩]

end X5OL
end X5mod_OL_Thm

section X5mod_AN_Scalar
open Real Set

namespace X5AN

/-- φ(c) = log(1-c) + 2c log 3 - log(1+c) is concave on [0,1/2]. -/
lemma phi_concave : ConcaveOn ℝ (Icc (0 : ℝ) (1 / 2))
    (fun c => Real.log (1 - c) + 2 * c * Real.log 3 - Real.log (1 + c)) := by
  have hint : interior (Icc (0 : ℝ) (1 / 2)) = Ioo 0 (1 / 2) := interior_Icc
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (f' := fun c => -(1 - c)⁻¹ + 2 * Real.log 3 - (1 + c)⁻¹)
    (f'' := fun c => -((1 - c) ^ 2)⁻¹ + ((1 + c) ^ 2)⁻¹) ?_ ?_ ?_ ?_
  · intro c hc
    have h1 : 0 < 1 - c := by linarith [hc.2]
    have h2 : 0 < 1 + c := by linarith [hc.1]
    refine ContinuousAt.continuousWithinAt ?_
    have h1' : 1 - c ≠ 0 := h1.ne'
    have h2' : 1 + c ≠ 0 := h2.ne'
    fun_prop (disch := assumption)
  · intro c hc
    rw [hint] at hc
    have h1 : 1 - c ≠ 0 := by linarith [hc.2]
    have h2 : 1 + c ≠ 0 := by linarith [hc.1]
    refine HasDerivAt.hasDerivWithinAt ?_
    have a := ((hasDerivAt_id c).const_sub 1).log h1
    have b := ((hasDerivAt_id c).const_add 1).log h2
    have d := ((hasDerivAt_id c).const_mul (2 : ℝ)).mul_const (Real.log 3)
    convert (a.add d).sub b using 1
    · funext x; simp <;> ring
    · simp <;> ring
  · intro c hc
    rw [hint] at hc
    have h1 : 1 - c ≠ 0 := by linarith [hc.2]
    have h2 : 1 + c ≠ 0 := by linarith [hc.1]
    refine HasDerivAt.hasDerivWithinAt ?_
    have a := (((hasDerivAt_id c).const_sub 1).inv h1).neg
    have b := ((hasDerivAt_id c).const_add 1).inv h2
    convert (a.add_const (2 * Real.log 3)).sub b using 1
    · funext x; simp <;> ring
    · simp <;> field_simp <;> ring
  · intro c hc
    rw [hint] at hc
    have h1 : 0 < 1 - c := by linarith [hc.2]
    have h2 : 0 < 1 + c := by linarith [hc.1]
    have : ((1 + c) ^ 2)⁻¹ ≤ ((1 - c) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (by nlinarith [hc.1])
    linarith

/-- (1+c) ≤ (1-c) 3^(2c) on [0,1/2]. -/
lemma numeric (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2) :
    1 + c ≤ (1 - c) * (3 : ℝ) ^ (2 * c) := by
  have hφ := phi_concave.2 (show (0 : ℝ) ∈ Icc 0 (1 / 2) from ⟨le_rfl, by norm_num⟩)
    (show (1 / 2 : ℝ) ∈ Icc 0 (1 / 2) from ⟨by norm_num, le_rfl⟩)
    (show 0 ≤ 1 - 2 * c by linarith) (show 0 ≤ 2 * c by linarith) (by ring : (1 - 2 * c) + 2 * c = 1)
  simp only [smul_eq_mul] at hφ
  have e0 : Real.log (1 - 0) + 2 * 0 * Real.log 3 - Real.log (1 + 0) = 0 := by simp
  have e1 : Real.log (1 - 1 / 2) + 2 * (1 / 2) * Real.log 3 - Real.log (1 + 1 / 2) = 0 := by
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num,
      Real.log_inv, Real.log_div (by norm_num) (by norm_num)]
    ring
  rw [e0, e1, mul_zero, mul_zero, add_zero, show (0 : ℝ) + 2 * c * (1 / 2) = c by ring] at hφ
  have h1 : 0 < 1 - c := by linarith
  have h2 : 0 < 1 + c := by linarith
  have key : Real.log (1 + c) ≤ Real.log ((1 - c) * (3 : ℝ) ^ (2 * c)) := by
    rw [Real.log_mul h1.ne' (by positivity), Real.log_rpow (by norm_num)]
    linarith
  exact (Real.log_le_log_iff h2 (by positivity)).1 key

/-- g(y) = y^c + y^(-c) is concave on [3,∞) for 0 < c ≤ 1/2. -/
lemma g_concave (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) :
    ConcaveOn ℝ (Ici (3 : ℝ)) (fun y => y ^ c + y ^ (-c)) := by
  have hint : interior (Ici (3 : ℝ)) = Ioi 3 := interior_Ici
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ici _)
    (f' := fun y => c * y ^ (c - 1) + -c * y ^ (-c - 1))
    (f'' := fun y => c * ((c - 1) * y ^ (c - 1 - 1)) + -c * ((-c - 1) * y ^ (-c - 1 - 1))) ?_ ?_ ?_ ?_
  · intro y hy
    have : (0 : ℝ) < y := by linarith [mem_Ici.1 hy]
    refine ContinuousAt.continuousWithinAt ?_
    exact (continuousAt_id.rpow_const (Or.inl this.ne')).add (continuousAt_id.rpow_const (Or.inl this.ne'))
  · intro y hy
    rw [hint] at hy
    have : y ≠ 0 := by linarith [mem_Ioi.1 hy]
    exact ((Real.hasDerivAt_rpow_const (Or.inl this)).add
      (Real.hasDerivAt_rpow_const (Or.inl this))).hasDerivWithinAt
  · intro y hy
    rw [hint] at hy
    have : y ≠ 0 := by linarith [mem_Ioi.1 hy]
    exact (((Real.hasDerivAt_rpow_const (Or.inl this)).const_mul c).add
      ((Real.hasDerivAt_rpow_const (Or.inl this)).const_mul (-c))).hasDerivWithinAt
  · intro y hy
    rw [hint] at hy
    have hy0 : 0 < y := by linarith [mem_Ioi.1 hy]
    have hn := numeric c hc0.le hc1
    have hpow : (3 : ℝ) ^ (2 * c) ≤ y ^ (2 * c) :=
      Real.rpow_le_rpow (by norm_num) (le_of_lt (mem_Ioi.1 hy)) (by linarith)
    have hsplit : y ^ (c - 1 - 1) = y ^ (2 * c) * y ^ (-c - 1 - 1) := by
      rw [← Real.rpow_add hy0]; ring_nf
    rw [hsplit]
    have hq : 0 < y ^ (-c - 1 - 1) := by positivity
    have : (1 + c) ≤ (1 - c) * y ^ (2 * c) := hn.trans (by nlinarith)
    nlinarith [mul_le_mul_of_nonneg_left this (le_of_lt (mul_pos hc0 hq))]

/-- 2(cosh v - 1) ≤ v²/ln 2 for |v| ≤ log 3 / 2. -/
lemma cosh_bound (v : ℝ) (hv : |v| ≤ Real.log 3 / 2) : 2 * (Real.cosh v - 1) ≤ v ^ 2 / Real.log 2 := by
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hl3 : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl30 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hv2 : v ^ 2 ≤ (Real.log 3 / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hv 2
  have hx : v ^ 2 / 2 < 1 := by nlinarith
  have hc := Real.cosh_le_exp_half_sq v
  rcases (sq_nonneg v).lt_or_eq with hpos | hz
  · have he := Real.exp_bound_div_one_sub_of_interval' (x := v ^ 2 / 2) (by positivity) hx
    have h1 : 0 < 1 - v ^ 2 / 2 := by linarith
    -- 2(exp x - 1) ≤ 2x/(1-x) and 1-x ≥ log 2
    have hlog : Real.log 2 ≤ 1 - v ^ 2 / 2 := by nlinarith
    have : 2 * (Real.cosh v - 1) ≤ 2 * (1 / (1 - v ^ 2 / 2) - 1) := by linarith
    calc 2 * (Real.cosh v - 1) ≤ 2 * (1 / (1 - v ^ 2 / 2) - 1) := this
      _ = v ^ 2 / (1 - v ^ 2 / 2) := by rw [div_sub_one h1.ne', mul_div_assoc']; congr 1; ring
      _ ≤ v ^ 2 / Real.log 2 := div_le_div_of_nonneg_left (sq_nonneg v) (by linarith) hlog
  · have : v = 0 := by nlinarith
    subst this; simp

end X5AN

namespace X5AN
open Real Set

lemma two_cosh_rpow (y c : ℝ) (hy : 0 < y) : y ^ c + y ^ (-c) = 2 * Real.cosh (c * Real.log y) := by
  rw [Real.cosh_eq, Real.rpow_def_of_pos hy, Real.rpow_def_of_pos hy]
  ring_nf

/-- Classical form of TCR Lemma 8. -/
lemma classical {K : Type*} [Fintype K] (p u : K → ℝ) (hp : ∀ k, 0 ≤ p k) (h1 : ∑ k, p k = 1)
    (β : ℝ) (hβ : 0 < β)
    (hη : 2 * β * Real.log (∑ k, p k * (Real.exp (u k / 2) + Real.exp (-(u k / 2)) + 1)) < Real.log 3 / 2) :
    -(∑ k, p k * u k) / Real.log 2 -
        4 * β * Real.logb 2 (∑ k, p k * (Real.exp (u k / 2) + Real.exp (-(u k / 2)) + 1)) ^ 2 ≤
      -(1 / β) * Real.logb 2 (∑ k, p k * Real.exp (β * u k)) := by
  set y : K → ℝ := fun k => Real.exp (u k / 2) + Real.exp (-(u k / 2)) + 1 with hy
  set η := ∑ k, p k * y k with hηdef
  set c := 2 * β with hc
  have hy3 : ∀ k, 3 ≤ y k := by
    intro k
    have := Real.one_le_cosh (u k / 2)
    rw [Real.cosh_eq] at this
    simp only [y]; linarith
  have hη3 : 3 ≤ η := by
    calc (3 : ℝ) = ∑ k, p k * 3 := by rw [← Finset.sum_mul, h1, one_mul]
      _ ≤ η := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hy3 k) (hp k)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlη : Real.log 3 ≤ Real.log η := Real.log_le_log (by norm_num) hη3
  have hc12 : c ≤ 1 / 2 := by
    by_contra h; push Not at h
    have : c * Real.log 3 ≤ c * Real.log η := mul_le_mul_of_nonneg_left hlη (by linarith)
    nlinarith
  have hc0 : 0 < c := by linarith
  -- positivity of S
  have hS : 0 < ∑ k, p k * Real.exp (β * u k) := by
    obtain ⟨k0, hk0⟩ : ∃ k, 0 < p k := by
      by_contra h; push Not at h
      have : ∑ k, p k ≤ 0 := Finset.sum_nonpos fun k _ => h k
      linarith
    exact Finset.sum_pos' (fun k _ => mul_nonneg (hp k) (Real.exp_pos _).le)
      ⟨k0, Finset.mem_univ _, mul_pos hk0 (Real.exp_pos _)⟩
  -- termwise bound
  have hterm : ∀ k, Real.exp (β * u k) - 1 ≤ β * u k + (y k ^ c + y k ^ (-c) - 2) := by
    intro k
    have hy0 : 0 < y k := by linarith [hy3 k]
    have e1 := Real.add_one_le_exp (-(β * u k))
    have hcosh : Real.cosh (β * u k) ≤ Real.cosh (c * Real.log (y k)) := by
      rw [Real.cosh_le_cosh]
      have hab : |u k| / 2 ≤ Real.log (y k) := by
        rw [Real.le_log_iff_exp_le hy0]
        rcases abs_cases (u k) with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h]; simp only [y]; linarith [Real.exp_pos (-(u k / 2))]
        · rw [h, neg_div]; simp only [y]; linarith [Real.exp_pos (u k / 2)]
      have hlog0 : 0 ≤ Real.log (y k) := Real.log_nonneg (by linarith [hy3 k])
      rw [abs_mul, abs_of_pos hβ, abs_of_nonneg (mul_nonneg hc0.le hlog0), hc]
      nlinarith
    rw [two_cosh_rpow _ _ hy0]
    have := Real.cosh_eq (β * u k)
    nlinarith
  have hjensen : ∑ k, p k * (y k ^ c + y k ^ (-c)) ≤ η ^ c + η ^ (-c) := by
    have := (g_concave c hc0 hc12).le_map_sum (t := Finset.univ) (w := p) (p := y)
      (fun k _ => hp k) h1 (fun k _ => mem_Ici.2 (hy3 k))
    simpa only [smul_eq_mul] using this
  have hSm1 : (∑ k, p k * Real.exp (β * u k)) - 1 ≤ β * ∑ k, p k * u k + (η ^ c + η ^ (-c) - 2) := by
    have e : (∑ k, p k * Real.exp (β * u k)) - 1 = ∑ k, p k * (Real.exp (β * u k) - 1) := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, h1]
    rw [e]
    calc ∑ k, p k * (Real.exp (β * u k) - 1) ≤ ∑ k, p k * (β * u k + (y k ^ c + y k ^ (-c) - 2)) :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hterm k) (hp k)
      _ = ∑ k, (β * (p k * u k) + p k * (y k ^ c + y k ^ (-c)) - 2 * p k) :=
          Finset.sum_congr rfl fun k _ => by ring
      _ = β * ∑ k, p k * u k + (∑ k, p k * (y k ^ c + y k ^ (-c)) - 2) := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1]; ring
      _ ≤ _ := by linarith
  have hη0 : 0 < η := by linarith
  have hcb := cosh_bound (c * Real.log η) (by
    rw [abs_of_nonneg (mul_nonneg hc0.le (by linarith))]; exact hη.le)
  rw [two_cosh_rpow _ _ hη0] at hSm1
  have hlog := Real.log_le_sub_one_of_pos hS
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl21 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  -- assemble
  have hL : Real.logb 2 η = Real.log η / Real.log 2 := rfl
  have hLS : Real.logb 2 (∑ k, p k * Real.exp (β * u k)) = Real.log (∑ k, p k * Real.exp (β * u k)) / Real.log 2 := rfl
  rw [hL, hLS]
  set S := ∑ k, p k * Real.exp (β * u k)
  set E := ∑ k, p k * u k
  set ℓ := Real.log η
  have hℓ0 : 0 ≤ ℓ := by linarith
  -- log S ≤ β E + c² ℓ² / ln 2
  have hA : Real.log S ≤ β * E + c ^ 2 * ℓ ^ 2 / Real.log 2 := by
    have : (c * ℓ) ^ 2 = c ^ 2 * ℓ ^ 2 := by ring
    rw [this] at hcb; linarith
  have key : Real.log S ≤ β * E + 4 * β ^ 2 * ℓ ^ 2 / Real.log 2 := by
    have : c ^ 2 = 4 * β ^ 2 := by rw [hc]; ring
    rw [this] at hA; exact hA
  have : -(1 / β) * ((β * E + 4 * β ^ 2 * ℓ ^ 2 / Real.log 2) / Real.log 2) ≤
      -(1 / β) * (Real.log S / Real.log 2) := by
    have hb : 0 < 1 / β := by positivity
    have := div_le_div_of_nonneg_right key hl2.le
    nlinarith
  calc -E / Real.log 2 - 4 * β * (ℓ / Real.log 2) ^ 2
      = -(1 / β) * ((β * E + 4 * β ^ 2 * ℓ ^ 2 / Real.log 2) / Real.log 2) := by
        field_simp; ring
    _ ≤ _ := this

end X5AN
end X5mod_AN_Scalar

section X5mod_AN_Thm
open Matrix Filter Set
open scoped ComplexOrder Topology ENNReal

namespace X5AN
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23 X5OL

attribute [local instance] Classical.propDecidable

section pairs
variable {I : Type*} [Fintype I] [DecidableEq I] (ν μ : I → ℝ) (W : I → I → ℝ)

noncomputable def pp (k : I × I) : ℝ := if 0 < ν k.1 ∧ 0 < μ k.2 then W k.1 k.2 * ν k.1 else 0
noncomputable def uu (k : I × I) : ℝ :=
  if 0 < ν k.1 ∧ 0 < μ k.2 then Real.log (ν k.1) - Real.log (μ k.2) else 0

lemma Φ_eq (t : ℝ) : Φ ν μ W t = ∑ k, pp ν μ W k * Real.exp ((t - 1) * uu ν μ k) := by
  unfold Φ
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [pp, uu]
  split_ifs with h
  · have e : Real.exp (t * Real.log (ν i) + (1 - t) * Real.log (μ j)) =
        Real.exp (Real.log (ν i)) * Real.exp ((t - 1) * (Real.log (ν i) - Real.log (μ j))) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [mul_assoc, e, Real.exp_log h.1]
  · simp

lemma Φ'_eq : Φ' ν μ W = ∑ k, pp ν μ W k * uu ν μ k := by
  unfold Φ'
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [pp, uu]
  split_ifs <;> ring

lemma pp_nonneg (hν : ∀ i, 0 ≤ ν i) (hW : ∀ i j, 0 ≤ W i j) (k : I × I) : 0 ≤ pp ν μ W k := by
  unfold pp; split_ifs
  · exact mul_nonneg (hW _ _) (hν _)
  · exact le_rfl

end pairs

lemma sum_exp_pos {K : Type*} [Fintype K] (p u : K → ℝ) (hp : ∀ k, 0 ≤ p k) (h1 : ∑ k, p k = 1) :
    0 < ∑ k, p k * Real.exp (u k) := by
  obtain ⟨k0, hk0⟩ : ∃ k, 0 < p k := by
    by_contra h; push Not at h
    have : ∑ k, p k ≤ 0 := Finset.sum_nonpos fun k _ => h k
    linarith
  exact Finset.sum_pos' (fun k _ => mul_nonneg (hp k) (Real.exp_pos _).le)
    ⟨k0, Finset.mem_univ _, mul_pos hk0 (Real.exp_pos _)⟩

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem main [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (heta : entropyConvergenceParameter rho sigma ≠ ⊤) (alpha : ℝ) (halpha : 1 < alpha)
    (halphaUpper : alpha < 1 + Real.logb 2 3 / (4 * Real.logb 2 (entropyConvergenceParameter rho sigma).toReal)) :
    fixedVonNeumann rho sigma -
      ((4 * (alpha - 1) * (Real.logb 2 (entropyConvergenceParameter rho sigma).toReal) ^ 2 : ℝ) : EReal) ≤
        finiteAlpha rho sigma alpha := by
  set N := identityTensorReference (A := A) sigma with hNdef
  have hNpsd : N.PosSemidef := N_psd sigma hsigma.1
  have hR := hrho.1.isHermitian
  have hN := hNpsd.isHermitian
  set ν := hR.eigenvalues
  set μ := hN.eigenvalues
  set W := w hR hN
  have hν : ∀ i, 0 ≤ ν i := hrho.1.eigenvalues_nonneg
  have hμ : ∀ j, 0 ≤ μ j := hNpsd.eigenvalues_nonneg
  have hW : ∀ i j, 0 ≤ W i j := w_nonneg hR hN
  have hrow : ∀ i, ∑ j, W i j = 1 := w_row hR hN
  have hcfc1 : cfc (fun _ : ℝ => (1 : ℝ)) N = 1 := cfc_const_one ℝ N hN.isSelfAdjoint
  have hsingle : ∀ f : ℝ → ℝ, (cfc f rho).trace.re = ∑ i, f (ν i) := by
    intro f
    have := tr_cfc_cfc hR hN f (fun _ => 1)
    rw [hcfc1, Matrix.mul_one] at this
    rw [this, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    simp only [Complex.ofReal_re, mul_one]
    rw [← Finset.mul_sum, hrow, mul_one]
  have htr : ∑ i, ν i = 1 := by
    have := hsingle (fun x => x)
    rw [cfc_id' ℝ rho hR.isSelfAdjoint, hrho.2] at this
    simpa using this.symm
  have hF : ∀ t : ℝ, 0 < t →
      (cfc (fun x : ℝ => x ^ t) rho * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) N).trace.re =
        Φ ν μ W t := fun t ht => tr_alpha hR hN hν hμ t ht
  by_cases hS : supportedBy rho N
  swap
  · exfalso; apply heta
    have h32 : finiteAlpha rho sigma (3 / 2) = ⊥ := by
      unfold finiteAlpha
      rw [if_neg (by norm_num), if_pos ⟨by norm_num, hS⟩]
    unfold entropyConvergenceParameter
    rw [h32, EReal.neg_bot, EReal.top_mul_coe_of_pos (by norm_num)]
    simp [exp2Extended]
  have hs : ∀ i j, ν i ≠ 0 → μ j = 0 → W i j = 0 := by
    intro i j hi hj
    simp only [W, w, supp_fwd hR hN hS i j hi hj, norm_zero]; norm_num
  have hΦ1 : Φ ν μ W 1 = 1 := by rw [Φ_one_supp ν μ W hν hμ hrow hs, htr]
  have hval : fixedVonNeumann rho sigma = ((-Φ' ν μ W / Real.log 2 : ℝ) : EReal) := by
    unfold fixedVonNeumann
    rw [if_pos hS, ← value_supp ν μ W hν hμ hrow hs]
    congr 2
    · have := tr_cfc_cfc hR hN (fun x => x) (fun x => Real.logb 2 x)
      rw [cfc_id' ℝ rho hR.isSelfAdjoint] at this
      rw [this, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.re_sum]; simp only [Complex.ofReal_re]; rfl
    · unfold QAlgorithms.vnEntropy
      rw [hsingle]
  set p := pp ν μ W
  set u := uu ν μ
  have hp : ∀ k, 0 ≤ p k := pp_nonneg ν μ W hν hW
  have hp1 : ∑ k, p k = 1 := by
    have := Φ_eq ν μ W 1
    simp only [sub_self, zero_mul, Real.exp_zero, mul_one] at this
    rw [← this, hΦ1]
  have hΦpos : ∀ t, 0 < Φ ν μ W t := fun t => by
    rw [Φ_eq]; exact sum_exp_pos p _ hp hp1
  -- value of finiteAlpha at t ≠ 1, t > 0
  have hFA : ∀ t : ℝ, 0 < t → t ≠ 1 →
      finiteAlpha rho sigma t = ((1 / (1 - t) * Real.logb 2 (Φ ν μ W t) : ℝ) : EReal) := by
    intro t ht ht1
    unfold finiteAlpha
    rw [if_neg ht1, if_neg (fun h => h.2 hS), hF t ht]
    unfold log2Extended
    rw [if_neg (hΦpos t).ne', ← EReal.coe_mul]
  have hexp2 : ∀ r : ℝ, exp2Extended (r : EReal) = ENNReal.ofReal ((2 : ℝ) ^ r) := by
    intro r; simp [exp2Extended]
  have hη : entropyConvergenceParameter rho sigma =
      ENNReal.ofReal (Φ ν μ W (3 / 2)) + ENNReal.ofReal (Φ ν μ W (1 / 2)) + 1 := by
    unfold entropyConvergenceParameter
    rw [hFA (3 / 2) (by norm_num) (by norm_num), hFA (1 / 2) (by norm_num) (by norm_num),
      ← EReal.coe_neg, ← EReal.coe_mul, ← EReal.coe_mul, hexp2, hexp2]
    congr 3
    · rw [show -(1 / (1 - 3 / 2) * Real.logb 2 (Φ ν μ W (3 / 2))) * (1 / 2) = Real.logb 2 (Φ ν μ W (3 / 2)) by
        ring, Real.rpow_logb (by norm_num) (by norm_num) (hΦpos _)]
    · rw [show 1 / (1 - 1 / 2) * Real.logb 2 (Φ ν μ W (1 / 2)) * (1 / 2) = Real.logb 2 (Φ ν μ W (1 / 2)) by
        ring, Real.rpow_logb (by norm_num) (by norm_num) (hΦpos _)]
  have hηr : (entropyConvergenceParameter rho sigma).toReal =
      ∑ k, p k * (Real.exp (u k / 2) + Real.exp (-(u k / 2)) + 1) := by
    rw [hη, ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_add (by simp) (by simp),
      ENNReal.toReal_ofReal (hΦpos _).le, ENNReal.toReal_ofReal (hΦpos _).le, ENNReal.toReal_one,
      Φ_eq, Φ_eq]
    simp only [mul_add, Finset.sum_add_distrib, mul_one, hp1]
    congr 2
    · refine Finset.sum_congr rfl fun k _ => ?_; congr 2; ring
    · refine Finset.sum_congr rfl fun k _ => ?_; congr 2; ring
  rw [hval, hFA alpha (by linarith) halpha.ne', hηr, ← EReal.coe_sub, EReal.coe_le_coe_iff, Φ_eq, Φ'_eq]
  rw [hηr] at halphaUpper
  set η := ∑ k, p k * (Real.exp (u k / 2) + Real.exp (-(u k / 2)) + 1) with hηdef
  have hβ : 0 < alpha - 1 := by linarith
  have hη3 : 3 ≤ η := by
    calc (3 : ℝ) = ∑ k, p k * 3 := by rw [← Finset.sum_mul, hp1, one_mul]
      _ ≤ η := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (by
          have := Real.one_le_cosh (u k / 2)
          rw [Real.cosh_eq] at this; linarith) (hp k)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLη : 0 < Real.logb 2 η := Real.logb_pos (by norm_num) (by linarith)
  have hcond : 2 * (alpha - 1) * Real.log η < Real.log 3 / 2 := by
    have h1 : (alpha - 1) * (4 * Real.logb 2 η) < Real.logb 2 3 := by
      have := sub_lt_iff_lt_add'.2 halphaUpper
      rwa [lt_div_iff₀ (by positivity)] at this
    simp only [Real.logb] at h1
    rw [show (alpha - 1) * (4 * (Real.log η / Real.log 2)) = (4 * (alpha - 1) * Real.log η) / Real.log 2 by ring,
      div_lt_div_iff_of_pos_right hl2] at h1
    linarith
  have := classical p u hp hp1 (alpha - 1) hβ hcond
  convert this using 2
  rw [show (1 : ℝ) - alpha = -(alpha - 1) by ring, div_neg]

end X5AN
end X5mod_AN_Thm

noncomputable section

open Filter

open scoped ENNReal ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

theorem solution {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (heta : entropyConvergenceParameter rho sigma ≠ ⊤) (alpha : ℝ) (halpha : 1 < alpha)
    (halphaUpper : alpha < 1 + Real.logb 2 3 / (4 * Real.logb 2 (entropyConvergenceParameter rho sigma).toReal)) :
    fixedVonNeumann rho sigma -
      ((4 * (alpha - 1) * (Real.logb 2 (entropyConvergenceParameter rho sigma).toReal) ^ 2 : ℝ) : EReal) ≤
        finiteAlpha rho sigma alpha :=
  X5AN.main rho sigma hrho hsigma heta alpha halpha halphaUpper

end
