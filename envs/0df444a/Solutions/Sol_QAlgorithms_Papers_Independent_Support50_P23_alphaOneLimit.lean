-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P23.alphaOneLimit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:56:56.353675+00:00
-- url     : https://prove2.me/submissions/298cbd9e-b6fa-43bc-b6ae-fd4078a827a9

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23
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

noncomputable section

open Filter

open scoped ENNReal ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

-- Exact accepted bodies. Other similarly named catalogue entries use different
-- smoothing, conditioning order, logarithm base, or channel-level objects.

open QAlgorithms.Papers.Independent.Gap20.P03 (fixedMin)

open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P69 (matrixPower)

theorem solution {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    Tendsto (finiteAlpha rho sigma)
      (nhdsWithin 1 {t : ℝ | 0 < t ∧ t ≠ 1}) (nhds (fixedVonNeumann rho sigma)) ∧
      alphaEntropy rho sigma 1 = fixedVonNeumann rho sigma :=
  X5OL.main rho sigma hrho hsigma

end
