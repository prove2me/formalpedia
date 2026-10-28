-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P23.fixedReferenceFiniteBlock
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T19:07:41.602987+00:00
-- url     : https://prove2.me/submissions/16b5b81a-704c-4eb1-a56d-5a56a0546832

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23
import Mathlib
import Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_smoothMinFromAlpha

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

/-- scalar form of all the quantities in Lemma 8, assuming finite η -/
lemma reduce [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (heta : entropyConvergenceParameter rho sigma ≠ ⊤) :
    ∃ p u : (A × B) × (A × B) → ℝ, (∀ k, 0 ≤ p k) ∧ ∑ k, p k = 1 ∧
      supportedBy rho (identityTensorReference (A := A) sigma) ∧
      (entropyConvergenceParameter rho sigma).toReal =
        ∑ k, p k * (Real.exp (u k / 2) + Real.exp (-(u k / 2)) + 1) ∧
      fixedVonNeumann rho sigma = ((-(∑ k, p k * u k) / Real.log 2 : ℝ) : EReal) ∧
      ∀ t : ℝ, 1 < t → finiteAlpha rho sigma t =
        ((1 / (1 - t) * Real.logb 2 (∑ k, p k * Real.exp ((t - 1) * u k)) : ℝ) : EReal) := by
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
  refine ⟨p, u, hp, hp1, hS, hηr, by rw [hval, Φ'_eq], fun t ht => by
    rw [hFA t (by linarith) ht.ne', Φ_eq]⟩

lemma eta3 [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (heta : entropyConvergenceParameter rho sigma ≠ ⊤) :
    3 ≤ (entropyConvergenceParameter rho sigma).toReal := by
  obtain ⟨p, u, hp, hp1, -, hηr, -⟩ := reduce rho sigma hrho hsigma heta
  rw [hηr]
  calc (3 : ℝ) = ∑ k, p k * 3 := by rw [← Finset.sum_mul, hp1, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (by
        have := Real.one_le_cosh (u k / 2)
        rw [Real.cosh_eq] at this; linarith) (hp k)

theorem main [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (heta : entropyConvergenceParameter rho sigma ≠ ⊤) (alpha : ℝ) (halpha : 1 < alpha)
    (halphaUpper : alpha < 1 + Real.logb 2 3 / (4 * Real.logb 2 (entropyConvergenceParameter rho sigma).toReal)) :
    fixedVonNeumann rho sigma -
      ((4 * (alpha - 1) * (Real.logb 2 (entropyConvergenceParameter rho sigma).toReal) ^ 2 : ℝ) : EReal) ≤
        finiteAlpha rho sigma alpha := by
  obtain ⟨p, u, hp, hp1, -, hηr, hval, hFA⟩ := reduce rho sigma hrho hsigma heta
  rw [hval, hFA alpha halpha, hηr, ← EReal.coe_sub, EReal.coe_le_coe_iff]
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

section X5mod_AI_Base
open Matrix

section X5mod_AI_Base

/-- conjugation by an isometry as a non-unital star algebra hom -/
noncomputable def x5ai_conjHom {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix n m ℂ) (hW : Wᴴ * W = 1) : Matrix m m ℂ →⋆ₙₐ[ℂ] Matrix n n ℂ where
  toFun X := W * X * Wᴴ
  map_smul' c X := by simp
  map_zero' := by simp
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_mul' X Y := by
    calc W * (X * Y) * Wᴴ = W * X * (Wᴴ * W) * Y * Wᴴ := by rw [hW]; simp [Matrix.mul_assoc]
      _ = _ := by simp [Matrix.mul_assoc]
  map_star' X := by simp [Matrix.star_eq_conjTranspose, conjTranspose_mul, Matrix.mul_assoc]

theorem x5ai_finite_cont {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ) (f : ℝ → ℝ) :
    ContinuousOn f (quasispectrum ℝ M) := by
  have : (quasispectrum ℝ M).Finite := by
    rw [quasispectrum_eq_spectrum_union_zero]
    exact (M.finite_real_spectrum).union (Set.finite_singleton 0)
  exact this.continuousOn _

theorem x5ai_finite_cont' {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ M) :=
  M.finite_real_spectrum.continuousOn _

theorem x5ai_conj {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix n m ℂ) (hW : Wᴴ * W = 1) (M : Matrix m m ℂ) (hM : M.IsHermitian)
    (f : ℝ → ℝ) (hf : f 0 = 0) : cfc f (W * M * Wᴴ) = W * cfc f M * Wᴴ := by
  have hWM : (W * M * Wᴴ).IsHermitian := by
    simp [IsHermitian, conjTranspose_mul, hM.eq, Matrix.mul_assoc]
  have hc : Continuous (x5ai_conjHom W hW) := by
    change Continuous fun X : Matrix m m ℂ => W * X * Wᴴ; fun_prop
  have h := NonUnitalStarAlgHom.map_cfcₙ (R := ℝ) (S := ℂ) (p := IsSelfAdjoint) (q := IsSelfAdjoint)
    (x5ai_conjHom W hW) f M (x5ai_finite_cont M f) hf hc hM.isSelfAdjoint hWM.isSelfAdjoint
  have h2 : W * cfcₙ f M * Wᴴ = cfcₙ f (W * M * Wᴴ) := h
  have e1 : cfcₙ f M = cfc f M := cfcₙ_eq_cfc (x5ai_finite_cont M f) hf
  have e2 : cfcₙ f (W * M * Wᴴ) = cfc f (W * M * Wᴴ) := cfcₙ_eq_cfc (x5ai_finite_cont (W * M * Wᴴ) f) hf
  rw [← e1, ← e2, h2]

/-- identity tensor X as a star algebra hom -/
noncomputable def x5ai_kronHom (C : Type*) {n : Type*} [Fintype C] [DecidableEq C] [Fintype n] [DecidableEq n] :
    Matrix n n ℂ →⋆ₐ[ℂ] Matrix (C × n) (C × n) ℂ where
  toFun X := Matrix.kronecker (1 : Matrix C C ℂ) X
  map_one' := Matrix.one_kronecker_one
  map_mul' X Y := by
    have := Matrix.mul_kronecker_mul (1 : Matrix C C ℂ) (1 : Matrix C C ℂ) X Y
    rw [Matrix.mul_one] at this
    exact this
  map_zero' := by simp
  map_add' X Y := by simp [Matrix.kronecker_add]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq]
    split_ifs <;> simp_all
  map_star' X := by simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]

theorem x5ai_kron (C : Type*) {n : Type*} [Fintype C] [DecidableEq C] [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian) (f : ℝ → ℝ) :
    cfc f (Matrix.kronecker (1 : Matrix C C ℂ) M) = Matrix.kronecker (1 : Matrix C C ℂ) (cfc f M) := by
  have hK : (Matrix.kronecker (1 : Matrix C C ℂ) M).IsHermitian := by
    simp [IsHermitian, Matrix.conjTranspose_kronecker, hM.eq]
  have h := StarAlgHom.map_cfc (R := ℝ) (S := ℂ) (p := IsSelfAdjoint) (q := IsSelfAdjoint)
    (x5ai_kronHom C (n := n)) f M (x5ai_finite_cont' M f)
    (by
      change Continuous fun X : Matrix n n ℂ => Matrix.kronecker (1 : Matrix C C ℂ) X
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Matrix.kronecker, Matrix.kroneckerMap_apply]
      exact continuous_const.mul ((continuous_apply _).comp (continuous_apply _)))
    hM.isSelfAdjoint hK.isSelfAdjoint
  exact h.symm

end X5mod_AI_Base
end X5mod_AI_Base

section X5mod_AD_Kron
open Matrix Polynomial
open scoped ComplexOrder Kronecker

namespace X5AD
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma aeval_diag (δ : ι → ℂ) (p : ℝ[X]) :
    aeval (diagonal δ) p = diagonal (fun k => aeval (δ k) p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, diagonal_add]
  | monomial k c =>
    simp only [aeval_monomial, Matrix.algebraMap_eq_diagonal, diagonal_pow, diagonal_mul_diagonal]
    rfl

lemma cfc_diag (d : ι → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun k => ((d k : ℝ) : ℂ))) = diagonal (fun k => ((f (d k) : ℝ) : ℂ)) := by
  set D := diagonal (fun k => ((d k : ℝ) : ℂ))
  have hfin : (spectrum ℝ D).Finite := D.finite_real_spectrum
  set s : Finset ℝ := Finset.univ.image d ∪ hfin.toFinset
  set p := Lagrange.interpolate s (fun x : ℝ => x) f
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h) hx
  have hD : IsSelfAdjoint D := by
    rw [← Matrix.isHermitian_iff_isSelfAdjoint]
    exact isHermitian_diagonal_of_self_adjoint _ (by ext k; simp [Complex.conj_ofReal])
  have h1 : cfc f D = cfc (fun x => p.eval x) D :=
    cfc_congr fun x hx => (hp x (Finset.mem_union_right _ (hfin.mem_toFinset.2 hx))).symm
  rw [h1, cfc_polynomial p D hD, aeval_diag]
  congr 1; ext k
  rw [show ((d k : ℝ) : ℂ) = algebraMap ℝ ℂ (d k) from rfl, aeval_algebraMap_apply,
    Polynomial.aeval_def, Algebra.algebraMap_self, ← Polynomial.eval,
    hp _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))]
  rfl

lemma spec {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    X = (hX.eigenvectorUnitary : Matrix ι ι ℂ) * diagonal (fun k => ((hX.eigenvalues k : ℝ) : ℂ)) *
      (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  conv_lhs => rw [← cfc_id' ℝ X hX.isSelfAdjoint]
  rw [hX.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

lemma cfc_spec {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    cfc f X = (hX.eigenvectorUnitary : Matrix ι ι ℂ) * diagonal (fun k => ((f (hX.eigenvalues k) : ℝ) : ℂ)) *
      (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  rw [hX.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

lemma uu {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * (hX.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
  Unitary.coe_star_mul_self _

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem cfc_kron {X : Matrix ι ι ℂ} {Y : Matrix κ κ ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (f : ℝ → ℝ) (hf0 : f 0 = 0) (hmul : ∀ x y, 0 ≤ x → 0 ≤ y → f (x * y) = f x * f y) :
    cfc f (X ⊗ₖ Y) = cfc f X ⊗ₖ cfc f Y := by
  have hXh := hX.isHermitian
  have hYh := hY.isHermitian
  set U := (hXh.eigenvectorUnitary : Matrix ι ι ℂ)
  set V := (hYh.eigenvectorUnitary : Matrix κ κ ℂ)
  set d := hXh.eigenvalues
  set e := hYh.eigenvalues
  have hW : (U ⊗ₖ V)ᴴ * (U ⊗ₖ V) = 1 := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, uu hXh, uu hYh, one_kronecker_one]
  have hDE : diagonal (fun k => ((d k : ℝ) : ℂ)) ⊗ₖ diagonal (fun k => ((e k : ℝ) : ℂ)) =
      diagonal (fun p : ι × κ => ((d p.1 * e p.2 : ℝ) : ℂ)) := by
    rw [diagonal_kronecker_diagonal]; congr 1; ext p; simp
  have hXY : X ⊗ₖ Y = (U ⊗ₖ V) * diagonal (fun p : ι × κ => ((d p.1 * e p.2 : ℝ) : ℂ)) * (U ⊗ₖ V)ᴴ := by
    conv_lhs => rw [spec hXh, spec hYh]
    rw [← hDE, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]
  have hDh : (diagonal (fun p : ι × κ => ((d p.1 * e p.2 : ℝ) : ℂ))).IsHermitian :=
    isHermitian_diagonal_of_self_adjoint _ (by ext k; simp [Complex.conj_ofReal])
  rw [hXY, x5ai_conj (U ⊗ₖ V) hW _ hDh f hf0, cfc_diag (fun p : ι × κ => d p.1 * e p.2) f,
    cfc_spec hXh, cfc_spec hYh]
  have hd : ∀ k, 0 ≤ d k := hX.eigenvalues_nonneg
  have he : ∀ k, 0 ≤ e k := hY.eigenvalues_nonneg
  have hDE' : diagonal (fun p : ι × κ => ((f (d p.1 * e p.2) : ℝ) : ℂ)) =
      diagonal (fun k => ((f (d k) : ℝ) : ℂ)) ⊗ₖ diagonal (fun k => ((f (e k) : ℝ) : ℂ)) := by
    rw [diagonal_kronecker_diagonal]; congr 1; ext p
    simp [hmul _ _ (hd p.1) (he p.2)]
  rw [hDE', conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]

end X5AD
end X5mod_AD_Kron

section X5mod_AD_Prod
open Matrix
open scoped ComplexOrder Kronecker

namespace X5AD
set_option linter.unusedSectionVars false
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- regrouping (A×C)×(B×D) → (A×B)×(C×D) -/
def eR : (A × C) × (B × D) ≃ (A × B) × (C × D) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun y := ((y.1.1, y.2.1), (y.1.2, y.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def Pm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (e : m ≃ n) : Matrix m n ℂ :=
  fun x y => if e x = y then 1 else 0

lemma Pm_conj {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (e : m ≃ n) (M : Matrix n n ℂ) :
    Pm e * M * (Pm e)ᴴ = M.submatrix e e := by
  ext x y
  simp [Pm, mul_apply, conjTranspose_apply]

lemma Pm_iso {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (e : m ≃ n) :
    (Pm e)ᴴ * Pm e = 1 := by
  ext k l
  simp only [Pm, mul_apply, conjTranspose_apply, one_apply]
  have : ∀ x, (star (if e x = k then (1 : ℂ) else 0)) * (if e x = l then 1 else 0) =
      if x = e.symm k then (if k = l then 1 else 0) else 0 := by
    intro x
    by_cases hx : x = e.symm k
    · subst hx; simp
    · have : e x ≠ k := fun h => hx (by rw [← h]; simp)
      simp [this, hx]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

variable (A B C D) in
noncomputable def PR : Matrix ((A × C) × (B × D)) ((A × B) × (C × D)) ℂ := Pm eR

lemma PR_conj (M : Matrix ((A × B) × (C × D)) ((A × B) × (C × D)) ℂ) :
    PR A B C D * M * (PR A B C D)ᴴ = M.submatrix eR eR := Pm_conj eR M

lemma PR_iso : (PR A B C D)ᴴ * PR A B C D = 1 := Pm_iso eR

lemma iP_eq (rho : Matrix (A × B) (A × B) ℂ) (tau : Matrix (C × D) (C × D) ℂ) :
    independentProduct rho tau = PR A B C D * (rho ⊗ₖ tau) * (PR A B C D)ᴴ := by
  rw [PR_conj]; rfl

lemma iT_eq (sigma : Matrix B B ℂ) (omega : Matrix D D ℂ) :
    identityTensorReference (A := A × C) (sigma ⊗ₖ omega) =
      PR A B C D * (identityTensorReference (A := A) sigma ⊗ₖ identityTensorReference (A := C) omega) *
        (PR A B C D)ᴴ := by
  rw [PR_conj]
  ext ⟨⟨a, c⟩, ⟨b, d⟩⟩ ⟨⟨a', c'⟩, ⟨b', d'⟩⟩
  simp only [identityTensorReference, submatrix_apply, kronecker_apply, one_apply, eR,
    Equiv.coe_fn_mk, Prod.mk.injEq]
  by_cases ha : a = a' <;> by_cases hc : c = c' <;> simp [ha, hc]

/-- the trace functional behind finiteAlpha -/
noncomputable def Tr {I : Type*} [Fintype I] [DecidableEq I] (R N : Matrix I I ℂ) (t : ℝ) : ℂ :=
  (cfc (fun x : ℝ => x ^ t) R * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) N).trace

lemma f_mul (t : ℝ) : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → (x * y) ^ t = x ^ t * y ^ t :=
  fun x y hx hy => Real.mul_rpow hx hy

lemma g_mul (t : ℝ) : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
    (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) (x * y) =
      (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) x * (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) y := by
  intro x y hx hy
  by_cases h0 : x = 0
  · simp [h0]
  by_cases h1 : y = 0
  · simp [h1]
  simp [h0, h1, Real.mul_rpow hx hy]

lemma Tr_conj {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (e : m ≃ n)
    (K1 K2 : Matrix n n ℂ) (h1 : K1.IsHermitian) (h2 : K2.IsHermitian) (t : ℝ) (ht : 0 < t) :
    Tr (Pm e * K1 * (Pm e)ᴴ) (Pm e * K2 * (Pm e)ᴴ) t = Tr K1 K2 t := by
  unfold Tr
  rw [x5ai_conj (Pm e) (Pm_iso e) K1 h1 _ (Real.zero_rpow ht.ne' : (0:ℝ) ^ t = 0),
    x5ai_conj (Pm e) (Pm_iso e) K2 h2 _ (by simp)]
  have : Pm e * cfc (fun x : ℝ => x ^ t) K1 * (Pm e)ᴴ *
      (Pm e * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) K2 * (Pm e)ᴴ) =
      Pm e * (cfc (fun x : ℝ => x ^ t) K1 * cfc (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t)) K2) *
        (Pm e)ᴴ := by
    simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (Pm e)ᴴ (Pm e), Pm_iso, Matrix.one_mul]
  rw [this, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Pm_iso, Matrix.mul_one]

lemma Tr_kron {X1 Y1 : Matrix (A × B) (A × B) ℂ} {X2 Y2 : Matrix (C × D) (C × D) ℂ}
    (hX1 : X1.PosSemidef) (hY1 : Y1.PosSemidef) (hX2 : X2.PosSemidef) (hY2 : Y2.PosSemidef)
    (t : ℝ) (ht : 0 < t) :
    Tr (X1 ⊗ₖ X2) (Y1 ⊗ₖ Y2) t = Tr X1 Y1 t * Tr X2 Y2 t := by
  unfold Tr
  rw [cfc_kron hX1 hX2 _ (Real.zero_rpow ht.ne' : (0:ℝ) ^ t = 0) (f_mul t), cfc_kron hY1 hY2 _ (by simp) (g_mul t),
    ← mul_kronecker_mul, trace_kronecker]

lemma iP_psd {rho : Matrix (A × B) (A × B) ℂ} {tau : Matrix (C × D) (C × D) ℂ}
    (h1 : rho.PosSemidef) (h2 : tau.PosSemidef) : (independentProduct rho tau).PosSemidef := by
  rw [iP_eq]; exact (h1.kronecker h2).mul_mul_conjTranspose_same _

lemma iP_density {rho : Matrix (A × B) (A × B) ℂ} {tau : Matrix (C × D) (C × D) ℂ}
    (h1 : IsDensityMatrix rho) (h2 : IsDensityMatrix tau) : IsDensityMatrix (independentProduct rho tau) := by
  refine ⟨iP_psd h1.1 h2.1, ?_⟩
  rw [iP_eq, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, PR_iso, Matrix.mul_one,
    trace_kronecker, h1.2, h2.2, one_mul]

lemma kron_density {sigma : Matrix B B ℂ} {omega : Matrix D D ℂ}
    (h1 : IsDensityMatrix sigma) (h2 : IsDensityMatrix omega) : IsDensityMatrix (sigma ⊗ₖ omega) :=
  ⟨h1.1.kronecker h2.1, by rw [trace_kronecker, h1.2, h2.2, one_mul]⟩

end X5AD
end X5mod_AD_Prod

section X5mod_AM_Conv
open Matrix Filter Set
open scoped Topology

namespace X5OL

variable {I : Type*} [Fintype I] [DecidableEq I]
set_option linter.unusedSectionVars false

section conv
variable (ν μ : I → ℝ) (W : I → I → ℝ) (hW : ∀ i j, 0 ≤ W i j)
include hW

lemma Φ_nonneg_term (t : ℝ) (i j : I) :
    0 ≤ (if 0 < ν i ∧ 0 < μ j then W i j * Real.exp (t * Real.log (ν i) + (1 - t) * Real.log (μ j)) else 0) := by
  split_ifs
  · exact mul_nonneg (hW i j) (Real.exp_pos _).le
  · exact le_rfl

lemma Φ_pos (h1 : 0 < Φ ν μ W 1) (t : ℝ) : 0 < Φ ν μ W t := by
  unfold Φ at h1 ⊢
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1.ne'
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  have hc : 0 < ν i ∧ 0 < μ j := by by_contra h; exact hj (if_neg h)
  have hw : W i j ≠ 0 := by intro h; apply hj; rw [if_pos hc, h, zero_mul]
  have hterm : 0 < (if 0 < ν i ∧ 0 < μ j then
      W i j * Real.exp (t * Real.log (ν i) + (1 - t) * Real.log (μ j)) else 0) := by
    rw [if_pos hc]; exact mul_pos ((hW i j).lt_of_ne (Ne.symm hw)) (Real.exp_pos _)
  refine lt_of_lt_of_le hterm ?_
  refine le_trans ?_ (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ =>
    Φ_nonneg_term ν μ W hW t i j) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => if 0 < ν i ∧ 0 < μ j then
      W i j * Real.exp (t * Real.log (ν i) + (1 - t) * Real.log (μ j)) else 0)
    (fun j _ => Φ_nonneg_term ν μ W hW t i j) (Finset.mem_univ j)

lemma Φ_holder (x y a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hX : 0 < Φ ν μ W x) (hY : 0 < Φ ν μ W y) :
    Φ ν μ W (a * x + b * y) ≤ Real.exp (a * Real.log (Φ ν μ W x) + b * Real.log (Φ ν μ W y)) := by
  set X := Φ ν μ W x
  set Y := Φ ν μ W y
  set E := Real.exp (a * Real.log X + b * Real.log Y)
  have key : ∀ i j, (if 0 < ν i ∧ 0 < μ j then
        W i j * Real.exp ((a * x + b * y) * Real.log (ν i) + (1 - (a * x + b * y)) * Real.log (μ j)) else 0) ≤
      E * (a * (if 0 < ν i ∧ 0 < μ j then
        W i j * Real.exp (x * Real.log (ν i) + (1 - x) * Real.log (μ j)) else 0) / X +
        b * (if 0 < ν i ∧ 0 < μ j then
        W i j * Real.exp (y * Real.log (ν i) + (1 - y) * Real.log (μ j)) else 0) / Y) := by
    intro i j
    split_ifs with hc
    · set ex := x * Real.log (ν i) + (1 - x) * Real.log (μ j)
      set ey := y * Real.log (ν i) + (1 - y) * Real.log (μ j)
      have he : (a * x + b * y) * Real.log (ν i) + (1 - (a * x + b * y)) * Real.log (μ j) =
          (a * Real.log X + b * Real.log Y) + (a * (ex - Real.log X) + b * (ey - Real.log Y)) := by
        simp only [ex, ey]
        have : b = 1 - a := by linarith
        subst this; ring
      have hcv := convexOn_exp.2 (mem_univ (ex - Real.log X)) (mem_univ (ey - Real.log Y)) ha hb hab
      simp only [smul_eq_mul] at hcv
      rw [Real.exp_sub, Real.exp_sub, Real.exp_log hX, Real.exp_log hY] at hcv
      rw [he, Real.exp_add]
      calc W i j * (E * Real.exp (a * (ex - Real.log X) + b * (ey - Real.log Y)))
          ≤ W i j * (E * (a * (Real.exp ex / X) + b * (Real.exp ey / Y))) := by
            gcongr
            exact hW i j
        _ = _ := by field_simp
    · simp
  calc Φ ν μ W (a * x + b * y) ≤ ∑ i, ∑ j, E * (a * (if 0 < ν i ∧ 0 < μ j then
        W i j * Real.exp (x * Real.log (ν i) + (1 - x) * Real.log (μ j)) else 0) / X +
        b * (if 0 < ν i ∧ 0 < μ j then
        W i j * Real.exp (y * Real.log (ν i) + (1 - y) * Real.log (μ j)) else 0) / Y) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = E * (a * X / X + b * Y / Y) := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div]
        rfl
    _ = E := by rw [mul_div_assoc, mul_div_assoc, div_self hX.ne', div_self hY.ne', mul_one, mul_one, hab,
          mul_one]

lemma L_convex (h1 : 0 < Φ ν μ W 1) : ConvexOn ℝ univ (fun t => Real.log (Φ ν μ W t)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hX := Φ_pos ν μ W hW h1 x
  have hY := Φ_pos ν μ W hW h1 y
  have := Φ_holder ν μ W hW x y a b ha hb hab hX hY
  calc Real.log (Φ ν μ W (a * x + b * y))
      ≤ Real.log (Real.exp (a * Real.log (Φ ν μ W x) + b * Real.log (Φ ν μ W y))) :=
        Real.log_le_log (Φ_pos ν μ W hW h1 _) this
    _ = _ := Real.log_exp _

end conv

end X5OL
end X5mod_AM_Conv

section X5mod_AM_Thm
open Matrix Filter Set
open scoped ComplexOrder Topology ENNReal

namespace X5OL
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem fa_anti [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    AntitoneOn (finiteAlpha rho sigma) (Ioi 0) := by
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
  have hFA : ∀ t : ℝ, 0 < t → t ≠ 1 → finiteAlpha rho sigma t =
      if 1 < t ∧ ¬ supportedBy rho N then ⊥
      else (((1 / (1 - t) : ℝ)) : EReal) * log2Extended (Φ ν μ W t) := by
    intro t ht ht1
    unfold finiteAlpha
    rw [if_neg ht1, hF t ht]
  have hF1 : finiteAlpha rho sigma 1 = fixedVonNeumann rho sigma := by
    unfold finiteAlpha; rw [if_pos rfl]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hS : supportedBy rho N
  · have hs : ∀ i j, ν i ≠ 0 → μ j = 0 → W i j = 0 := by
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
    set L := fun t => Real.log (Φ ν μ W t) with hLdef
    have hconv := L_convex ν μ W hW (by rw [hΦ1]; norm_num)
    have hL : HasDerivAt L (Φ' ν μ W) 1 := by
      have := (Φ_deriv ν μ W).log (by rw [hΦ1]; norm_num)
      rwa [hΦ1, div_one] at this
    have hL1 : L 1 = 0 := by simp [hLdef, hΦ1]
    set h : ℝ → ℝ := fun t => if t = 1 then Φ' ν μ W else slope L 1 t with hhdef
    have hg : ∀ t, 0 < t → finiteAlpha rho sigma t = ((-(h t) / Real.log 2 : ℝ) : EReal) := by
      intro t ht
      by_cases ht1 : t = 1
      · subst ht1; rw [hF1, hval]; simp [hhdef]
      · rw [hFA t ht ht1, if_neg (fun h => h.2 hS)]
        have hp := Φ_pos ν μ W hW (by rw [hΦ1]; norm_num) t
        unfold log2Extended
        rw [if_neg hp.ne', ← EReal.coe_mul]
        congr 1
        simp only [hhdef, if_neg ht1, slope_def_field, sub_zero, hLdef, Real.logb, hΦ1, Real.log_one]
        have : t - 1 ≠ 0 := sub_ne_zero.2 ht1
        have : 1 - t ≠ 0 := fun h' => this (by linarith)
        field_simp
        ring
    have hmono : Monotone h := by
      intro s t hst
      rcases hst.lt_or_eq with hst | rfl
      · simp only [hhdef]
        by_cases hs1 : s = 1
        · subst hs1
          rw [if_pos rfl, if_neg hst.ne']
          exact hconv.le_slope_of_hasDerivAt (mem_univ _) (mem_univ _) hst hL
        · by_cases ht1 : t = 1
          · subst ht1
            rw [if_neg hs1, if_pos rfl, slope_comm]
            exact hconv.slope_le_of_hasDerivAt (mem_univ _) (mem_univ _) hst hL
          · rw [if_neg hs1, if_neg ht1]
            exact hconv.slope_mono (mem_univ _) ⟨mem_univ _, hs1⟩ ⟨mem_univ _, ht1⟩ hst.le
      · exact le_rfl
    intro s hs t ht hst
    rw [hg s hs, hg t ht, EReal.coe_le_coe_iff]
    have := hmono hst
    rw [div_le_div_iff_of_pos_right hl2]
    linarith
  · have hval : fixedVonNeumann rho sigma = ⊥ := by unfold fixedVonNeumann; rw [if_neg hS]
    have hex : ∃ i j, ν i ≠ 0 ∧ μ j = 0 ∧ W i j ≠ 0 := by
      by_contra hne
      push Not at hne
      apply hS
      refine supp_bwd hR hN fun i j hi hj => ?_
      have := hne i j hi hj
      simp only [W, w] at this
      exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
    have hlt : Φ ν μ W 1 < 1 := htr ▸ Φ_one_lt ν μ W hν hμ hW hrow hex
    have hbot : ∀ t, 1 ≤ t → finiteAlpha rho sigma t = ⊥ := by
      intro t ht
      rcases ht.lt_or_eq with ht | rfl
      · rw [hFA t (by linarith) ht.ne', if_pos ⟨ht, hS⟩]
      · rw [hF1, hval]
    have hΦnn : 0 ≤ Φ ν μ W 1 := by
      rw [Φ_one]
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
        split_ifs
        · exact mul_nonneg (hW i j) (hν i)
        · exact le_rfl
    intro s hs t ht hst
    by_cases ht1 : 1 ≤ t
    · rw [hbot t ht1]; exact bot_le
    push Not at ht1
    have hs1 : s < 1 := lt_of_le_of_lt hst ht1
    have hs0 : (0 : ℝ) < s := hs
    have ht0 : (0 : ℝ) < t := ht
    rw [hFA t ht0 ht1.ne, hFA s hs0 hs1.ne, if_neg (fun h => absurd h.1 (not_lt.2 ht1.le)),
      if_neg (fun h => absurd h.1 (not_lt.2 hs1.le))]
    rcases hΦnn.eq_or_lt with h0 | h0
    · rw [Φ_zero ν μ W hν hμ hW h0.symm t]
      unfold log2Extended
      rw [if_pos rfl, EReal.coe_mul_bot_of_pos (by rw [one_div]; exact inv_pos.2 (by linarith))]
      exact bot_le
    · have hpt := Φ_pos ν μ W hW h0 t
      have hps := Φ_pos ν μ W hW h0 s
      unfold log2Extended
      rw [if_neg hpt.ne', if_neg hps.ne', ← EReal.coe_mul, ← EReal.coe_mul, EReal.coe_le_coe_iff]
      have hconv := L_convex ν μ W hW h0
      have hL1 : Real.log (Φ ν μ W 1) < 0 := Real.log_neg h0 hlt
      set θ := (1 - t) / (1 - s)
      have h1s : 0 < 1 - s := by linarith
      have h1t : 0 < 1 - t := by linarith
      have hθ0 : 0 ≤ θ := div_nonneg h1t.le h1s.le
      have hθ1 : 0 ≤ 1 - θ := by
        simp only [θ]; rw [sub_nonneg, div_le_one h1s]; linarith
      have hc := hconv.2 (mem_univ s) (mem_univ 1) hθ0 hθ1 (by ring)
      simp only [smul_eq_mul, mul_one] at hc
      have ht' : θ * s + (1 - θ) = t := by simp only [θ]; field_simp; ring
      rw [ht'] at hc
      have hc2 : Real.log (Φ ν μ W t) ≤ θ * Real.log (Φ ν μ W s) := by
        have := mul_nonpos_of_nonneg_of_nonpos hθ1 hL1.le
        linarith
      unfold Real.logb
      have hθs : θ * (1 - s) = 1 - t := by simp only [θ]; field_simp
      have k : Real.log (Φ ν μ W t) * (1 - s) ≤ Real.log (Φ ν μ W s) * (1 - t) := by
        rw [← hθs]
        have := mul_le_mul_of_nonneg_right hc2 h1s.le
        linarith
      have e1 : ∀ (x y : ℝ), 1 / x * (y / Real.log 2) = (y / x) / Real.log 2 := fun x y => by ring
      rw [e1, e1]
      refine div_le_div_of_nonneg_right ?_ hl2.le
      rw [div_le_div_iff₀ h1t h1s]
      linarith

end X5OL

namespace X5OL
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

theorem am_main {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    Antitone (alphaEntropy rho sigma) := by
  have hg := fa_anti rho sigma hrho hsigma
  have hsup : ∀ t : ℝ, 0 < t → finiteAlpha rho sigma t ≤ alphaEntropy rho sigma 0 := by
    intro t ht
    unfold alphaEntropy; rw [if_pos rfl]
    exact le_sSup ⟨t, ht, rfl⟩
  have hinf : ∀ t : ℝ, 0 < t → alphaEntropy rho sigma ⊤ ≤ finiteAlpha rho sigma t := by
    intro t ht
    unfold alphaEntropy; rw [if_neg ENNReal.top_ne_zero, if_pos rfl]
    exact sInf_le ⟨t, ht, rfl⟩
  have hfin : ∀ a : ℝ≥0∞, a ≠ 0 → a ≠ ⊤ →
      alphaEntropy rho sigma a = finiteAlpha rho sigma a.toReal ∧ 0 < a.toReal := by
    intro a h0 hT
    refine ⟨?_, ENNReal.toReal_pos h0 hT⟩
    unfold alphaEntropy; rw [if_neg h0, if_neg hT]
  intro a b hab
  by_cases ha0 : a = 0
  · subst ha0
    by_cases hb0 : b = 0
    · subst hb0; exact le_rfl
    by_cases hbT : b = ⊤
    · subst hbT; exact (hinf 1 one_pos).trans (hsup 1 one_pos)
    obtain ⟨e, hp⟩ := hfin b hb0 hbT
    rw [e]; exact hsup _ hp
  by_cases haT : a = ⊤
  · subst haT; rw [top_le_iff.1 hab]
  obtain ⟨ea, hpa⟩ := hfin a ha0 haT
  have hb0 : b ≠ 0 := fun h => ha0 (le_antisymm (h ▸ hab) bot_le)
  by_cases hbT : b = ⊤
  · subst hbT; rw [ea]; exact hinf _ hpa
  obtain ⟨eb, hpb⟩ := hfin b hb0 hbT
  rw [ea, eb]
  exact hg hpa hpb (ENNReal.toReal_mono hbT hab)

end X5OL
end X5mod_AM_Thm

section X5mod_AD_Fin
open Matrix Filter Set
open scoped ComplexOrder Kronecker Topology

namespace X5AD
set_option linter.unusedSectionVars false
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23 X5OL

attribute [local instance] Classical.propDecidable

section single
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- spectral facts for one pair -/
theorem pack (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    (∀ t, Tr rho (identityTensorReference (A := A) sigma) t =
        (((Tr rho (identityTensorReference (A := A) sigma) t).re : ℝ) : ℂ)) ∧
    (∀ t, 0 < t → 0 ≤ (Tr rho (identityTensorReference (A := A) sigma) t).re) ∧
    (supportedBy rho (identityTensorReference (A := A) sigma) ↔
      (Tr rho (identityTensorReference (A := A) sigma) 1).re = 1) ∧
    (Tr rho (identityTensorReference (A := A) sigma) 1).re ≤ 1 ∧
    (supportedBy rho (identityTensorReference (A := A) sigma) →
      ∀ t, 0 < t → 0 < (Tr rho (identityTensorReference (A := A) sigma) t).re) := by
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
  have hT : ∀ t, 0 < t → (Tr rho N t).re = Φ ν μ W t := fun t ht => tr_alpha hR hN hν hμ t ht
  have hΦnn : ∀ t, 0 ≤ Φ ν μ W t := fun t =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Φ_nonneg_term ν μ W hW t i j
  have hsupp : supportedBy rho N ↔ Φ ν μ W 1 = 1 := by
    constructor
    · intro hS
      have hs : ∀ i j, ν i ≠ 0 → μ j = 0 → W i j = 0 := by
        intro i j hi hj
        simp only [W, w, supp_fwd hR hN hS i j hi hj, norm_zero]; norm_num
      rw [Φ_one_supp ν μ W hν hμ hrow hs, htr]
    · intro h1
      by_contra hS
      have hex : ∃ i j, ν i ≠ 0 ∧ μ j = 0 ∧ W i j ≠ 0 := by
        by_contra hne
        push Not at hne
        apply hS
        refine supp_bwd hR hN fun i j hi hj => ?_
        have := hne i j hi hj
        simp only [W, w] at this
        exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
      have := Φ_one_lt ν μ W hν hμ hW hrow hex
      rw [htr] at this; linarith
  have hle1 : Φ ν μ W 1 ≤ 1 := by
    by_cases hS : supportedBy rho N
    · exact (hsupp.1 hS).le
    · have hex : ∃ i j, ν i ≠ 0 ∧ μ j = 0 ∧ W i j ≠ 0 := by
        by_contra hne
        push Not at hne
        apply hS
        refine supp_bwd hR hN fun i j hi hj => ?_
        have := hne i j hi hj
        simp only [W, w] at this
        exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
      have := Φ_one_lt ν μ W hν hμ hW hrow hex
      rw [htr] at this; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    unfold Tr
    rw [tr_cfc_cfc hR hN]
    simp only [← Complex.ofReal_sum, Complex.ofReal_re]
  · intro t ht; rw [hT t ht]; exact hΦnn t
  · rw [hT 1 one_pos]; exact hsupp
  · rw [hT 1 one_pos]; exact hle1
  · intro hS t ht
    rw [hT t ht]
    exact Φ_pos ν μ W hW (by rw [hsupp.1 hS]; norm_num) t

end single

lemma L_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    log2Extended (x * y) = log2Extended x + log2Extended y := by
  unfold log2Extended
  by_cases h0 : x = 0
  · simp [h0]
  by_cases h1 : y = 0
  · simp [h1]
  rw [if_neg (mul_ne_zero h0 h1), if_neg h0, if_neg h1, Real.logb_mul h0 h1, EReal.coe_add]

lemma L_ne_top (x : ℝ) : log2Extended x ≠ ⊤ := by
  unfold log2Extended; split_ifs <;> simp

lemma emul_add (c : ℝ) (u v : EReal) (hu : u ≠ ⊤) (hv : v ≠ ⊤) :
    (c : EReal) * (u + v) = c * u + c * v := by
  induction u using EReal.rec with
  | top => exact absurd rfl hu
  | bot =>
    induction v using EReal.rec with
    | top => exact absurd rfl hv
    | bot =>
      rcases lt_trichotomy c 0 with h | rfl | h
      · simp [EReal.coe_mul_bot_of_neg h]
      · simp
      · simp [EReal.coe_mul_bot_of_pos h]
    | coe s =>
      rcases lt_trichotomy c 0 with h | rfl | h
      · simp [EReal.coe_mul_bot_of_neg h, ← EReal.coe_mul]
      · simp
      · simp [EReal.coe_mul_bot_of_pos h, ← EReal.coe_mul]
  | coe r =>
    induction v using EReal.rec with
    | top => exact absurd rfl hv
    | bot =>
      rcases lt_trichotomy c 0 with h | rfl | h
      · simp [EReal.coe_mul_bot_of_neg h, ← EReal.coe_mul]
      · simp
      · simp [EReal.coe_mul_bot_of_pos h, ← EReal.coe_mul]
    | coe s => rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, mul_add]

end X5AD
end X5mod_AD_Fin

section X5mod_AD_Add
open Matrix Filter Set
open scoped ComplexOrder Kronecker Topology

namespace X5AD
set_option linter.unusedSectionVars false
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23 X5OL

attribute [local instance] Classical.propDecidable

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

lemma fa_form {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ) (t : ℝ) (ht1 : t ≠ 1) :
    finiteAlpha rho sigma t =
      if 1 < t ∧ ¬ supportedBy rho (identityTensorReference (A := A) sigma) then ⊥
      else ((1 / (1 - t) : ℝ) : EReal) * log2Extended (Tr rho (identityTensorReference (A := A) sigma) t).re := by
  unfold finiteAlpha Tr; rw [if_neg ht1]

lemma fa_ne_top {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) (t : ℝ) (ht : 0 < t) :
    finiteAlpha rho sigma t ≠ ⊤ := by
  obtain ⟨-, -, -, -, h5⟩ := pack rho sigma hrho hsigma
  by_cases ht1 : t = 1
  · subst ht1; unfold finiteAlpha fixedVonNeumann; rw [if_pos rfl]; split_ifs
    · exact EReal.coe_ne_top _
    · simp
  rw [fa_form rho sigma t ht1]
  split_ifs with h
  · simp
  · rcases lt_or_gt_of_ne ht1 with hlt | hgt
    · have hc : (0 : ℝ) < 1 / (1 - t) := by rw [one_div]; exact inv_pos.2 (by linarith)
      unfold log2Extended; split_ifs
      · rw [EReal.coe_mul_bot_of_pos hc]; simp
      · rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
    · have hS : supportedBy rho (identityTensorReference (A := A) sigma) := by
        by_contra hS; exact h ⟨hgt, hS⟩
      unfold log2Extended; rw [if_neg (h5 hS t ht).ne', ← EReal.coe_mul]; exact EReal.coe_ne_top _

lemma Tr_PR (K1 K2 : Matrix ((A × B) × (C × D)) ((A × B) × (C × D)) ℂ)
    (h1 : K1.IsHermitian) (h2 : K2.IsHermitian) (t : ℝ) (ht : 0 < t) :
    Tr (PR A B C D * K1 * (PR A B C D)ᴴ) (PR A B C D * K2 * (PR A B C D)ᴴ) t = Tr K1 K2 t :=
  Tr_conj eR K1 K2 h1 h2 t ht

theorem fa_add [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (tau : Matrix (C × D) (C × D) ℂ) (omega : Matrix D D ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (htau : IsDensityMatrix tau) (homega : IsDensityMatrix omega)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≠ 1) :
    finiteAlpha (independentProduct rho tau) (sigma ⊗ₖ omega) t =
      finiteAlpha rho sigma t + finiteAlpha tau omega t := by
  set R := independentProduct rho tau
  set N1 := identityTensorReference (A := A) sigma
  set N2 := identityTensorReference (A := C) omega
  set NR := identityTensorReference (A := A × C) (sigma ⊗ₖ omega)
  have hR : IsDensityMatrix R := iP_density hrho htau
  have hM : IsDensityMatrix (sigma ⊗ₖ omega) := kron_density hsigma homega
  have hN1 : N1.PosSemidef := N_psd sigma hsigma.1
  have hN2 : N2.PosSemidef := N_psd omega homega.1
  obtain ⟨p1, p2, p3, p4, p5⟩ := pack rho sigma hrho hsigma
  obtain ⟨q1, q2, q3, q4, q5⟩ := pack tau omega htau homega
  obtain ⟨r1, r2, r3, r4, r5⟩ := pack R (sigma ⊗ₖ omega) hR hM
  have hTR : ∀ s, 0 < s → (Tr R NR s).re = (Tr rho N1 s).re * (Tr tau N2 s).re := by
    intro s hs
    have : Tr R NR s = Tr rho N1 s * Tr tau N2 s := by
      simp only [R, NR]
      rw [iP_eq, iT_eq, Tr_PR _ _ (hrho.1.kronecker htau.1).isHermitian
        (hN1.kronecker hN2).isHermitian s hs, Tr_kron hrho.1 hN1 htau.1 hN2 s hs]
    rw [this, p1 s, q1 s, ← Complex.ofReal_mul, Complex.ofReal_re]
    simp only [Complex.ofReal_re]
  have hsuppR : supportedBy R NR ↔ supportedBy rho N1 ∧ supportedBy tau N2 := by
    rw [r3, p3, q3, hTR 1 one_pos]
    have a0 := p2 1 one_pos
    have b0 := q2 1 one_pos
    constructor
    · intro h
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩; rw [h1, h2, one_mul]
  rw [fa_form R _ t ht1, fa_form rho sigma t ht1, fa_form tau omega t ht1]
  by_cases hbad : 1 < t ∧ ¬ (supportedBy rho N1 ∧ supportedBy tau N2)
  · rw [if_pos ⟨hbad.1, by rw [hsuppR]; exact hbad.2⟩]
    have h1 := fa_ne_top rho sigma hrho hsigma t ht
    have h2 := fa_ne_top tau omega htau homega t ht
    rw [fa_form rho sigma t ht1] at h1
    rw [fa_form tau omega t ht1] at h2
    by_cases hs1 : supportedBy rho N1
    · have hs2 : ¬ supportedBy tau N2 := fun h => hbad.2 ⟨hs1, h⟩
      rw [if_neg (fun h => h.2 hs1), if_pos ⟨hbad.1, hs2⟩, EReal.add_bot]
    · rw [if_pos ⟨hbad.1, hs1⟩, EReal.bot_add]
  · rw [if_neg (by rw [hsuppR]; exact hbad)]
    have c1 : ¬ (1 < t ∧ ¬ supportedBy rho N1) := fun h => hbad ⟨h.1, fun h' => h.2 h'.1⟩
    have c2 : ¬ (1 < t ∧ ¬ supportedBy tau N2) := fun h => hbad ⟨h.1, fun h' => h.2 h'.2⟩
    rw [if_neg c1, if_neg c2, hTR t ht, L_mul (p2 t ht) (q2 t ht), emul_add _ _ _ (L_ne_top _) (L_ne_top _)]

end X5AD
end X5mod_AD_Add

section X5mod_AD_Ends
open Matrix Filter Set
open scoped ComplexOrder Kronecker Topology ENNReal

namespace X5AD
set_option linter.unusedSectionVars false
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23 X5OL

attribute [local instance] Classical.propDecidable

/-- abstract endpoint lemmas -/
lemma sup_add (F G : ℝ → EReal) (hF : AntitoneOn F (Ioi 0)) (hG : AntitoneOn G (Ioi 0)) :
    sSup {h : EReal | ∃ t : ℝ, 0 < t ∧ h = F t + G t} =
      sSup {h : EReal | ∃ t : ℝ, 0 < t ∧ h = F t} + sSup {h : EReal | ∃ t : ℝ, 0 < t ∧ h = G t} := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨t, ht, rfl⟩
    exact add_le_add (le_sSup ⟨t, ht, rfl⟩) (le_sSup ⟨t, ht, rfl⟩)
  · refine EReal.add_le_of_forall_lt fun a ha b hb => ?_
    obtain ⟨_, ⟨s, hs, rfl⟩, has⟩ := lt_sSup_iff.1 ha
    obtain ⟨_, ⟨t, ht, rfl⟩, hbt⟩ := lt_sSup_iff.1 hb
    set m := min s t
    have hm : (0 : ℝ) < m := lt_min hs ht
    refine le_trans (add_le_add (has.le.trans (hF hm hs (min_le_left _ _)))
      (hbt.le.trans (hG hm ht (min_le_right _ _)))) (le_sSup ⟨m, hm, rfl⟩)

lemma inf_add (F G : ℝ → EReal) (hF : AntitoneOn F (Ioi 0)) (hG : AntitoneOn G (Ioi 0))
    (hFt : ∀ t, 0 < t → F t ≠ ⊤) (hGt : ∀ t, 0 < t → G t ≠ ⊤) :
    sInf {h : EReal | ∃ t : ℝ, 0 < t ∧ h = F t + G t} =
      sInf {h : EReal | ∃ t : ℝ, 0 < t ∧ h = F t} + sInf {h : EReal | ∃ t : ℝ, 0 < t ∧ h = G t} := by
  have hIF : sInf {h : EReal | ∃ t : ℝ, 0 < t ∧ h = F t} ≠ ⊤ :=
    ne_top_of_le_ne_top (hFt 1 one_pos) (sInf_le ⟨1, one_pos, rfl⟩)
  have hIG : sInf {h : EReal | ∃ t : ℝ, 0 < t ∧ h = G t} ≠ ⊤ :=
    ne_top_of_le_ne_top (hGt 1 one_pos) (sInf_le ⟨1, one_pos, rfl⟩)
  apply le_antisymm
  · refine EReal.le_add_of_forall_gt (Or.inr hIG) (Or.inl hIF) fun a ha b hb => ?_
    obtain ⟨_, ⟨s, hs, rfl⟩, has⟩ := sInf_lt_iff.1 ha
    obtain ⟨_, ⟨t, ht, rfl⟩, hbt⟩ := sInf_lt_iff.1 hb
    set m := max s t
    have hm : (0 : ℝ) < m := lt_max_of_lt_left hs
    exact le_trans (sInf_le ⟨m, hm, rfl⟩) (add_le_add ((hF hs hm (le_max_left _ _)).trans has.le)
      ((hG ht hm (le_max_right _ _)).trans hbt.le))
  · refine le_sInf ?_
    rintro _ ⟨t, ht, rfl⟩
    exact add_le_add (sInf_le ⟨t, ht, rfl⟩) (sInf_le ⟨t, ht, rfl⟩)

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

theorem fa_add_all [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (tau : Matrix (C × D) (C × D) ℂ) (omega : Matrix D D ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (htau : IsDensityMatrix tau) (homega : IsDensityMatrix omega)
    (t : ℝ) (ht : 0 < t) :
    finiteAlpha (independentProduct rho tau) (sigma ⊗ₖ omega) t =
      finiteAlpha rho sigma t + finiteAlpha tau omega t := by
  by_cases ht1 : t ≠ 1
  · exact fa_add rho sigma tau omega hrho hsigma htau homega t ht ht1
  push Not at ht1; subst ht1
  have hR : IsDensityMatrix (independentProduct rho tau) := iP_density hrho htau
  have hM : IsDensityMatrix (sigma ⊗ₖ omega) := kron_density hsigma homega
  set S := {t : ℝ | 0 < t ∧ t ≠ 1}
  have hne : (𝓝[S] (1 : ℝ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot]
    have : closure (Ioo (0 : ℝ) 1) ⊆ closure S :=
      closure_mono fun t ht => ⟨ht.1, ht.2.ne⟩
    exact this (by rw [closure_Ioo (by norm_num)]; exact ⟨by norm_num, le_rfl⟩)
  have l1 := (X5OL.main rho sigma hrho hsigma).1
  have l2 := (X5OL.main tau omega htau homega).1
  have lR := (X5OL.main _ _ hR hM).1
  have e1 : ∀ X Y, finiteAlpha (A := A) (B := B) X Y 1 = fixedVonNeumann X Y := fun X Y => by
    unfold finiteAlpha; rw [if_pos rfl]
  have e2 : ∀ X Y, finiteAlpha (A := C) (B := D) X Y 1 = fixedVonNeumann X Y := fun X Y => by
    unfold finiteAlpha; rw [if_pos rfl]
  have e3 : ∀ X Y, finiteAlpha (A := A × C) (B := B × D) X Y 1 = fixedVonNeumann X Y := fun X Y => by
    unfold finiteAlpha; rw [if_pos rfl]
  have n1 : fixedVonNeumann rho sigma ≠ ⊤ := by rw [← e1]; exact fa_ne_top _ _ hrho hsigma 1 one_pos
  have n2 : fixedVonNeumann tau omega ≠ ⊤ := by rw [← e2]; exact fa_ne_top _ _ htau homega 1 one_pos
  have hsum : Tendsto (fun t => finiteAlpha rho sigma t + finiteAlpha tau omega t) (𝓝[S] 1)
      (𝓝 (fixedVonNeumann rho sigma + fixedVonNeumann tau omega)) :=
    (EReal.continuousAt_add (p := (fixedVonNeumann rho sigma, fixedVonNeumann tau omega))
      (Or.inl n1) (Or.inr n2)).tendsto.comp (l1.prodMk_nhds l2)
  have hR' : Tendsto (finiteAlpha (independentProduct rho tau) (sigma ⊗ₖ omega)) (𝓝[S] 1)
      (𝓝 (fixedVonNeumann rho sigma + fixedVonNeumann tau omega)) := by
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (fa_add rho sigma tau omega hrho hsigma htau homega t ht.1 ht.2).symm
  rw [e1, e2, e3]
  exact tendsto_nhds_unique lR hR'

theorem ae_add [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (tau : Matrix (C × D) (C × D) ℂ) (omega : Matrix D D ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (htau : IsDensityMatrix tau) (homega : IsDensityMatrix omega) (alpha : ℝ≥0∞) :
    alphaEntropy (independentProduct rho tau) (sigma ⊗ₖ omega) alpha =
      alphaEntropy rho sigma alpha + alphaEntropy tau omega alpha := by
  have hadd := fa_add_all rho sigma tau omega hrho hsigma htau homega
  have hset : ∀ (P : EReal → EReal → Prop), {h : EReal | ∃ t : ℝ, 0 < t ∧
      h = finiteAlpha (independentProduct rho tau) (sigma ⊗ₖ omega) t} =
      {h : EReal | ∃ t : ℝ, 0 < t ∧ h = finiteAlpha rho sigma t + finiteAlpha tau omega t} := by
    intro _
    ext h; constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, hadd t ht⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, (hadd t ht).symm⟩
  unfold alphaEntropy
  split_ifs with h0 hT
  · rw [hset (fun _ _ => True)]
    exact sup_add _ _ (fa_anti rho sigma hrho hsigma) (fa_anti tau omega htau homega)
  · rw [hset (fun _ _ => True)]
    exact inf_add _ _ (fa_anti rho sigma hrho hsigma) (fa_anti tau omega htau homega)
      (fun t ht => fa_ne_top _ _ hrho hsigma t ht) (fun t ht => fa_ne_top _ _ htau homega t ht)
  · exact hadd _ (ENNReal.toReal_pos h0 hT)

end X5AD
end X5mod_AD_Ends

section X5mod_AI_Main
open Matrix
open scoped ENNReal ComplexOrder

namespace X5AI
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

theorem iso_kron (U : Matrix C A ℂ) (V : Matrix D B ℂ)
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1) :
    (Matrix.kronecker U V)ᴴ * Matrix.kronecker U V = 1 := by
  unfold Matrix.kronecker
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, hU, hV, one_kronecker_one]

theorem cfc_ref (U : Matrix C A ℂ) (V : Matrix D B ℂ)
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1)
    (sigma : Matrix B B ℂ) (hs : sigma.IsHermitian) (g : ℝ → ℝ) (hg : g 0 = 0) :
    (Matrix.kronecker U V)ᴴ * cfc g (identityTensorReference (A := C) (V * sigma * Vᴴ)) *
      Matrix.kronecker U V = cfc g (identityTensorReference (A := A) sigma) := by
  unfold identityTensorReference
  rw [x5ai_kron, x5ai_conj V hV sigma hs g hg, x5ai_kron _ _ hs]
  unfold Matrix.kronecker
  rw [conjTranspose_kronecker,
    ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, hU]
  · congr 1
    calc Vᴴ * (V * cfc g sigma * Vᴴ) * V = (Vᴴ * V) * cfc g sigma * (Vᴴ * V) := by
          simp [Matrix.mul_assoc]
      _ = _ := by rw [hV]; simp
  · simp [IsHermitian, conjTranspose_mul, hs.eq, Matrix.mul_assoc]

theorem trace_eq (U : Matrix C A ℂ) (V : Matrix D B ℂ)
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1)
    (rho : Matrix (A × B) (A × B) ℂ) (hr : rho.IsHermitian)
    (sigma : Matrix B B ℂ) (hs : sigma.IsHermitian) (f g : ℝ → ℝ) (hf : f 0 = 0) (hg : g 0 = 0) :
    (cfc f (Matrix.kronecker U V * rho * (Matrix.kronecker U V)ᴴ) *
      cfc g (identityTensorReference (A := C) (V * sigma * Vᴴ))).trace =
    (cfc f rho * cfc g (identityTensorReference (A := A) sigma)).trace := by
  rw [x5ai_conj _ (iso_kron U V hU hV) rho hr f hf, ← cfc_ref U V hU hV sigma hs g hg]
  set W := Matrix.kronecker U V
  set G := cfc g (identityTensorReference (A := C) (V * sigma * Vᴴ))
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc]

theorem intertw (U : Matrix C A ℂ) (V : Matrix D B ℂ) (hV : V.conjTranspose * V = 1)
    (sigma : Matrix B B ℂ) :
    identityTensorReference (A := C) (V * sigma * Vᴴ) * Matrix.kronecker U V =
      Matrix.kronecker U V * identityTensorReference (A := A) sigma := by
  unfold identityTensorReference Matrix.kronecker
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hV,
    Matrix.mul_one]

theorem supp_iff (U : Matrix C A ℂ) (V : Matrix D B ℂ)
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1)
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ) (hs : sigma.IsHermitian) :
    supportedBy (Matrix.kronecker U V * rho * (Matrix.kronecker U V)ᴴ)
        (identityTensorReference (A := C) (V * sigma * Vᴴ)) ↔
      supportedBy rho (identityTensorReference (A := A) sigma) := by
  have hW := iso_kron U V hU hV
  have hI := intertw U V hV sigma
  set W := Matrix.kronecker U V
  set N' := identityTensorReference (A := C) (V * sigma * Vᴴ)
  set N := identityTensorReference (A := A) sigma
  have hNh : Nᴴ = N := by
    simp [N, identityTensorReference, Matrix.kronecker, conjTranspose_kronecker, hs.eq]
  have hN'h : N'ᴴ = N' := by
    simp [N', identityTensorReference, Matrix.kronecker, conjTranspose_kronecker, conjTranspose_mul,
      hs.eq, Matrix.mul_assoc]
  have hI' : Wᴴ * N' = N * Wᴴ := by
    have := congrArg conjTranspose hI
    rw [conjTranspose_mul, conjTranspose_mul, hNh, hN'h] at this
    exact this
  unfold supportedBy
  constructor
  · intro h x hx
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx ⊢
    have h1 : N' *ᵥ (W *ᵥ x) = 0 := by rw [mulVec_mulVec, hI, ← mulVec_mulVec, hx, mulVec_zero]
    have h2 := h (show W *ᵥ x ∈ _ from by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact h1)
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h2
    rw [mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hW, Matrix.mul_one] at h2
    have h3 := congrArg (Wᴴ *ᵥ ·) h2
    simp only [mulVec_mulVec, ← Matrix.mul_assoc, hW, Matrix.one_mul, mulVec_zero] at h3
    exact h3
  · intro h y hy
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hy ⊢
    have h1 : N *ᵥ (Wᴴ *ᵥ y) = 0 := by rw [mulVec_mulVec, ← hI', ← mulVec_mulVec, hy, mulVec_zero]
    have h2 := h (show Wᴴ *ᵥ y ∈ _ from by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact h1)
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h2
    rw [← mulVec_mulVec, ← mulVec_mulVec, h2, mulVec_zero]

theorem vn_eq (U : Matrix C A ℂ) (V : Matrix D B ℂ)
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1)
    (rho : Matrix (A × B) (A × B) ℂ) (hr : rho.IsHermitian) :
    vnEntropy (Matrix.kronecker U V * rho * (Matrix.kronecker U V)ᴴ) = vnEntropy rho := by
  unfold vnEntropy
  rw [x5ai_conj _ (iso_kron U V hU hV) rho hr _ (by simp), Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    iso_kron U V hU hV, Matrix.one_mul]

theorem trace_eq0 (U : Matrix C A ℂ) (V : Matrix D B ℂ)
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1)
    (rho : Matrix (A × B) (A × B) ℂ)
    (sigma : Matrix B B ℂ) (hs : sigma.IsHermitian) (g : ℝ → ℝ) (hg : g 0 = 0) :
    ((Matrix.kronecker U V * rho * (Matrix.kronecker U V)ᴴ) *
      cfc g (identityTensorReference (A := C) (V * sigma * Vᴴ))).trace =
    (rho * cfc g (identityTensorReference (A := A) sigma)).trace := by
  rw [← cfc_ref U V hU hV sigma hs g hg]
  set W := Matrix.kronecker U V
  set G := cfc g (identityTensorReference (A := C) (V * sigma * Vᴴ))
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc]

theorem fa_eq (U : Matrix C A ℂ) (V : Matrix D B ℂ)
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1)
    (rho : Matrix (A × B) (A × B) ℂ) (hr : rho.IsHermitian)
    (sigma : Matrix B B ℂ) (hs : sigma.IsHermitian) (t : ℝ) (ht : 0 < t) :
    finiteAlpha (Matrix.kronecker U V * rho * (Matrix.kronecker U V)ᴴ) (V * sigma * Vᴴ) t =
      finiteAlpha rho sigma t := by
  unfold finiteAlpha fixedVonNeumann
  have hsupp := supp_iff U V hU hV rho sigma hs
  by_cases hS : supportedBy rho (identityTensorReference (A := A) sigma)
  · have hS' := hsupp.2 hS
    simp only [hS, hS', not_true_eq_false, and_false, if_false, if_true]
    simp only [vn_eq U V hU hV rho hr,
      trace_eq0 U V hU hV rho sigma hs (fun x : ℝ => Real.logb 2 x) (by simp),
      trace_eq U V hU hV rho hr sigma hs (fun x : ℝ => x ^ t) (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t))
        (Real.zero_rpow ht.ne') (by simp)]

  · have hS' : ¬ _ := fun h => hS (hsupp.1 h)
    simp only [hS, hS', not_false_eq_true, and_true, if_false, if_true]
    simp only [vn_eq U V hU hV rho hr,
      trace_eq0 U V hU hV rho sigma hs (fun x : ℝ => Real.logb 2 x) (by simp),
      trace_eq U V hU hV rho hr sigma hs (fun x : ℝ => x ^ t) (fun x : ℝ => if x = 0 then 0 else x ^ (1 - t))
        (Real.zero_rpow ht.ne') (by simp)]

end X5AI

theorem x5ai_main {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : QAlgorithms.IsDensityMatrix rho) (hsigma : QAlgorithms.IsDensityMatrix sigma)
    (U : Matrix C A ℂ) (V : Matrix D B ℂ)
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1) (alpha : ℝ≥0∞) :
    QAlgorithms.Papers.Independent.Support50.P23.alphaEntropy rho sigma alpha =
      QAlgorithms.Papers.Independent.Support50.P23.alphaEntropy
        (Matrix.kronecker U V * rho * (Matrix.kronecker U V).conjTranspose)
        (V * sigma * V.conjTranspose) alpha := by
  have hr := hrho.1.isHermitian
  have hs := hsigma.1.isHermitian
  have key := fun t (ht : (0 : ℝ) < t) => X5AI.fa_eq U V hU hV rho hr sigma hs t ht
  unfold QAlgorithms.Papers.Independent.Support50.P23.alphaEntropy
  split_ifs with h0 h1
  · congr 1; ext h
    exact ⟨fun ⟨t, ht, e⟩ => ⟨t, ht, e.trans (key t ht).symm⟩, fun ⟨t, ht, e⟩ => ⟨t, ht, e.trans (key t ht)⟩⟩
  · congr 1; ext h
    exact ⟨fun ⟨t, ht, e⟩ => ⟨t, ht, e.trans (key t ht).symm⟩, fun ⟨t, ht, e⟩ => ⟨t, ht, e.trans (key t ht)⟩⟩
  · exact (key _ (ENNReal.toReal_pos h0 h1)).symm
end X5mod_AI_Main

section X5mod_AD_Pow
open Matrix Filter Set
open scoped ComplexOrder Kronecker Topology ENNReal

namespace X5AD
set_option linter.unusedSectionVars false
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23 X5OL
open QAlgorithms.Papers.Independent.Information100.P69 (matrixPower)

attribute [local instance] Classical.propDecidable

lemma Pm_kron {m n m' n' : Type*} [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
    [DecidableEq n] [DecidableEq n'] (e : m ≃ n) (e' : m' ≃ n') :
    (Pm e ⊗ₖ Pm e') = Pm (e.prodCongr e') := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [kronecker_apply, Pm, Equiv.prodCongr_apply, Prod.map_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- split off the last site -/
def eS (X : Type*) (n : ℕ) : (Fin (n + 1) → X) ≃ (Fin n → X) × X where
  toFun x := (Fin.init x, x (Fin.last n))
  invFun p := Fin.snoc p.1 p.2
  left_inv x := Fin.snoc_init_self x
  right_inv p := by simp

def e1 (X : Type*) : (Fin 1 → X) ≃ X := Equiv.funUnique (Fin 1) X

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

lemma conj_density {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (W : Matrix m n ℂ) (hW : Wᴴ * W = 1) {M : Matrix n n ℂ} (hM : IsDensityMatrix M) :
    IsDensityMatrix (W * M * Wᴴ) :=
  ⟨hM.1.mul_mul_conjTranspose_same W, by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hW, Matrix.mul_one, hM.2]⟩

lemma jp_succ (rho : Matrix (A × B) (A × B) ℂ) (n : ℕ) :
    jointPower rho (n + 1) = (Pm (eS A n) ⊗ₖ Pm (eS B n)) * independentProduct (jointPower rho n) rho *
      (Pm (eS A n) ⊗ₖ Pm (eS B n))ᴴ := by
  rw [Pm_kron, Pm_conj]
  ext x y
  simp only [jointPower, submatrix_apply, Equiv.prodCongr_apply, Prod.map_apply, eS, Equiv.coe_fn_mk,
    independentProduct]
  rw [Fin.prod_univ_castSucc]
  rfl

lemma mp_succ (sigma : Matrix B B ℂ) (n : ℕ) :
    matrixPower sigma (n + 1) = Pm (eS B n) * (matrixPower sigma n ⊗ₖ sigma) * (Pm (eS B n))ᴴ := by
  rw [Pm_conj]
  ext x y
  simp only [matrixPower, submatrix_apply, eS, Equiv.coe_fn_mk, kronecker_apply]
  rw [Fin.prod_univ_castSucc]
  rfl

lemma jp_one (rho : Matrix (A × B) (A × B) ℂ) :
    jointPower rho 1 = (Pm (e1 A) ⊗ₖ Pm (e1 B)) * rho * (Pm (e1 A) ⊗ₖ Pm (e1 B))ᴴ := by
  rw [Pm_kron, Pm_conj]
  ext x y
  simp [jointPower, e1]
  rfl

lemma mp_one (sigma : Matrix B B ℂ) :
    matrixPower sigma 1 = Pm (e1 B) * sigma * (Pm (e1 B))ᴴ := by
  rw [Pm_conj]
  ext x y
  simp [matrixPower, e1]

lemma kron_iso {m n m' n' : Type*} [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
    [DecidableEq m] [DecidableEq n] [DecidableEq m'] [DecidableEq n'] (e : m ≃ n) (e' : m' ≃ n') :
    (Pm e ⊗ₖ Pm e')ᴴ * (Pm e ⊗ₖ Pm e') = 1 := by
  rw [Pm_kron]; exact Pm_iso _

theorem pow_all [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) (alpha : ℝ≥0∞) :
    ∀ n : ℕ, 0 < n →
      IsDensityMatrix (jointPower rho n) ∧ IsDensityMatrix (matrixPower sigma n) ∧
      alphaEntropy (jointPower rho n) (matrixPower sigma n) alpha = n • alphaEntropy rho sigma alpha := by
  intro n hn
  induction n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨?_, ?_, ?_⟩
      · rw [jp_one]; exact conj_density _ (kron_iso _ _) hrho
      · rw [mp_one]; exact conj_density _ (Pm_iso _) hsigma
      · have := x5ai_main rho sigma hrho hsigma (Pm (e1 A)) (Pm (e1 B)) (Pm_iso _) (Pm_iso _) alpha
        rw [jp_one, mp_one]
        exact this.symm.trans (one_smul ℕ _).symm
    obtain ⟨h1, h2, h3⟩ := ih hk
    have hP := iP_density h1 hrho
    have hK := kron_density h2 hsigma
    refine ⟨?_, ?_, ?_⟩
    · rw [jp_succ]; exact conj_density _ (kron_iso _ _) hP
    · rw [mp_succ]; exact conj_density _ (Pm_iso _) hK
    · have := x5ai_main _ _ hP hK (Pm (eS A k)) (Pm (eS B k)) (Pm_iso _) (Pm_iso _) alpha
      rw [jp_succ, mp_succ, succ_nsmul, ← h3, ← ae_add _ _ _ _ h1 h2 hrho hsigma alpha]
      exact this.symm

end X5AD
end X5mod_AD_Pow

section X5mod_RF_Thm
open Matrix Filter Set
open scoped ComplexOrder Topology ENNReal

namespace X5RF
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23
open QAlgorithms.Papers.Independent.Gap20.P03 (fixedMin)
open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)
open QAlgorithms.Papers.Independent.Information100.P69 (matrixPower)

attribute [local instance] Classical.propDecidable

/-- for ε ≥ 1 the zero operator is in the ball and has fixed min-entropy +∞ -/
lemma smooth_top {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ) (hsigma : sigma.PosSemidef)
    (epsilon : ℝ) (he : 1 ≤ epsilon) : sineSmoothFixedMin rho sigma epsilon = ⊤ := by
  have hball : inBall rho 0 epsilon := by
    refine ⟨⟨PosSemidef.zero, by simp⟩, ?_⟩
    unfold fidelityDistance
    refine le_trans ?_ he
    rw [Real.sqrt_le_one]
    nlinarith [sq_nonneg (rootFidelity rho 0)]
  have hmin : fixedMin (0 : Matrix (A × B) (A × B) ℂ) sigma = ⊤ := by
    rw [EReal.eq_top_iff_forall_lt]
    intro y
    refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (lt_add_one y)) (le_sSup ⟨y + 1, rfl, ?_⟩)
    rw [sub_zero]
    exact (Matrix.PosSemidef.kronecker Matrix.PosSemidef.one hsigma).smul
      (Complex.zero_le_real.2 (Real.rpow_nonneg (by norm_num) _))
  refine eq_top_iff.2 ?_
  rw [← hmin]
  exact le_sSup ⟨0, hball, rfl⟩

lemma log2_three : (5 / 2 : ℝ) < Real.logb 2 3 ^ 2 := by
  have h : (19 / 12 : ℝ) < Real.logb 2 3 := by
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
    have : ((2 : ℝ) ^ (19 / 12 : ℝ)) ^ (12 : ℕ) < (3 : ℝ) ^ (12 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    exact lt_of_pow_lt_pow_left₀ 12 (by norm_num) this
  nlinarith

lemma nsmul_coe (n : ℕ) (x : ℝ) : n • (x : EReal) = ((n * x : ℝ) : EReal) := by
  induction n with
  | zero => simp
  | succ k ih => rw [succ_nsmul, ih, ← EReal.coe_add]; congr 1; push_cast; ring

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

lemma fa_of_ae (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ) (t : ℝ) (ht : 0 < t) :
    alphaEntropy rho sigma (ENNReal.ofReal t) = finiteAlpha rho sigma t := by
  unfold alphaEntropy
  rw [if_neg (by simpa using ht), if_neg ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal ht.le]

theorem main [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (n : ℕ) (hn : 0 < n) :
    ((epsilon < 1 ∧ entropyConvergenceParameter rho sigma ≠ ⊤ ∧
        (8 / 5 : ℝ) * Real.logb 2 (2 / epsilon ^ 2) ≤ (n : ℝ)) →
      fixedVonNeumann rho sigma -
        ((aepBlockError epsilon (entropyConvergenceParameter rho sigma) / Real.sqrt (n : ℝ) : ℝ) : EReal) ≤
          (((n : ℝ)⁻¹ : ℝ) : EReal) *
            sineSmoothFixedMin (jointPower rho n) (matrixPower sigma n) epsilon) ∧
    (¬ supportedBy rho (identityTensorReference (A := A) sigma) →
      fixedVonNeumann rho sigma = ⊥ ∧ fixedVonNeumann rho sigma ≤
        (((n : ℝ)⁻¹ : ℝ) : EReal) *
          sineSmoothFixedMin (jointPower rho n) (matrixPower sigma n) epsilon) ∧
    (1 ≤ epsilon → sineSmoothFixedMin (jointPower rho n) (matrixPower sigma n) epsilon = ⊤) := by
  have hpow := fun α => X5AD.pow_all rho sigma hrho hsigma α n hn
  obtain ⟨hX, hY, -⟩ := hpow 1
  refine ⟨?_, fun hS => ?_, fun he => smooth_top _ _ hY.1 epsilon he⟩
  swap
  · have : fixedVonNeumann rho sigma = ⊥ := by unfold fixedVonNeumann; rw [if_neg hS]
    exact ⟨this, this ▸ bot_le⟩
  rintro ⟨he1, heta, hthr⟩
  obtain ⟨p, u, hp, hp1, -, hηr, hval, hFA⟩ := X5AN.reduce rho sigma hrho hsigma heta
  have hη3 := X5AN.eta3 rho sigma hrho hsigma heta
  set η := (entropyConvergenceParameter rho sigma).toReal with hηdef
  set L := Real.logb 2 η with hL
  set g := Real.logb 2 (2 / epsilon ^ 2) with hg
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hL3 : Real.logb 2 3 ≤ L := Real.logb_le_logb_of_le (by norm_num) (by norm_num) hη3
  have hl3 := log2_three
  have hl30 : 1 < Real.logb 2 3 := by
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]; norm_num
  have hL0 : 0 < L := by linarith
  have hg0 : 0 < g := by
    refine Real.logb_pos (by norm_num) ?_
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  set s := Real.sqrt (g / n) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (div_pos hg0 hn0)
  have hss : s ^ 2 = g / n := Real.sq_sqrt (div_pos hg0 hn0).le
  have hs58 : s ^ 2 ≤ 5 / 8 := by
    rw [hss, div_le_iff₀ hn0]; linarith
  set β := s / (2 * L) with hβ
  have hβ0 : 0 < β := by positivity
  have hsl : s < Real.logb 2 3 / 2 := by
    have h1 : 0 < Real.logb 2 3 := by linarith
    nlinarith
  have hβup : 1 + β < 1 + Real.logb 2 3 / (4 * L) := by
    rw [hβ, add_lt_add_iff_left, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hβ2 : 1 + β ≤ 2 := by
    have : s ≤ 1 := by nlinarith
    rw [hβ]
    have : s / (2 * L) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  -- Lemma 8
  have h8 := X5AN.main rho sigma hrho hsigma heta (1 + β) (by linarith) hβup
  -- Theorem 7 on the n-fold product
  have h7 := smoothMinFromAlpha (jointPower rho n) (matrixPower sigma n) hX hY epsilon (1 + β)
    hepsilon (by linarith) hβ2
  -- additivity
  obtain ⟨-, -, hadd⟩ := hpow (ENNReal.ofReal (1 + β))
  rw [fa_of_ae _ _ _ (by linarith), fa_of_ae _ _ _ (by linarith)] at hadd
  rw [hadd, hFA _ (by linarith)] at h7
  rw [hval, hFA _ (by linarith)] at h8
  rw [hval]
  set F := 1 / (1 - (1 + β)) * Real.logb 2 (∑ k, p k * Real.exp ((1 + β - 1) * u k))
  set H := -(∑ k, p k * u k) / Real.log 2
  rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at h8
  rw [← hηdef, ← hL, show 1 + β - 1 = β by ring] at h8
  rw [nsmul_coe, ← EReal.coe_sub,
    show 1 + β - 1 = β by ring] at h7
  have h7' := mul_le_mul_of_nonneg_left h7 (EReal.coe_nonneg.2 (inv_nonneg.2 hn0.le))
  rw [← EReal.coe_mul] at h7'
  refine le_trans ?_ h7'
  rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
  -- real arithmetic
  have herr : aepBlockError epsilon (entropyConvergenceParameter rho sigma) / Real.sqrt n = 4 * L * s := by
    unfold aepBlockError
    rw [← hL, ← hg, hs, Real.sqrt_div' _ hn0.le]
    ring
  rw [herr]
  have e1 : (n : ℝ)⁻¹ * (n * F - g / β) = F - g / (n * β) := by
    field_simp
  rw [e1]
  have e2 : g / (n * β) = 2 * L * s := by
    rw [hβ, show g = s ^ 2 * n by rw [hss]; field_simp]
    field_simp
  have e3 : 4 * β * L ^ 2 = 2 * L * s := by
    rw [hβ]; field_simp; ring
  rw [e2]
  linarith

end X5RF
end X5mod_RF_Thm

noncomputable section

open Filter

open scoped ENNReal ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

open QAlgorithms.Papers.Independent.Information100.P69 (matrixPower)

theorem solution {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (n : ℕ) (hn : 0 < n) :
    ((epsilon < 1 ∧ entropyConvergenceParameter rho sigma ≠ ⊤ ∧
        (8 / 5 : ℝ) * Real.logb 2 (2 / epsilon ^ 2) ≤ (n : ℝ)) →
      fixedVonNeumann rho sigma -
        ((aepBlockError epsilon (entropyConvergenceParameter rho sigma) / Real.sqrt (n : ℝ) : ℝ) : EReal) ≤
          (((n : ℝ)⁻¹ : ℝ) : EReal) *
            sineSmoothFixedMin (jointPower rho n) (matrixPower sigma n) epsilon) ∧
    (¬ supportedBy rho (identityTensorReference (A := A) sigma) →
      fixedVonNeumann rho sigma = ⊥ ∧ fixedVonNeumann rho sigma ≤
        (((n : ℝ)⁻¹ : ℝ) : EReal) *
          sineSmoothFixedMin (jointPower rho n) (matrixPower sigma n) epsilon) ∧
    (1 ≤ epsilon → sineSmoothFixedMin (jointPower rho n) (matrixPower sigma n) epsilon = ⊤) :=
  X5RF.main rho sigma hrho hsigma epsilon hepsilon n hn

end
