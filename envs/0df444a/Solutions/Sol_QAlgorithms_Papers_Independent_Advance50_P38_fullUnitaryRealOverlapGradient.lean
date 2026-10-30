-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P38.fullUnitaryRealOverlapGradient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:46:43.159715+00:00
-- url     : https://prove2.me/submissions/6bff6dee-4b57-4782-b419-1993926f49f4

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38
namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

end

end QAlgorithms.Papers.Independent.Advance50.P38

open QAlgorithms.Papers.Independent.Advance50.P38
open QAlgorithms.Papers.Independent.Advance50 (P38.comm)
open scoped Matrix Matrix.Norms.Operator ComplexOrder

section s38
variable {n : ℕ}

lemma s38_det_exp_herm (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (z : ℂ) :
    (NormedSpace.exp (z • H)).det = NormedSpace.exp (z * H.trace) := by
  have hUm : (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) ∈ unitary (Matrix (Fin n) (Fin n) ℂ) :=
    hH.eigenvectorUnitary.2
  have hsU := Unitary.mul_star_self_of_mem hUm
  have hUs := Unitary.star_mul_self_of_mem hUm
  have hs := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  have htr : H.trace = ∑ j, (hH.eigenvalues j : ℂ) := by
    rw [hH.trace_eq_sum_eigenvalues]; simp
  rw [htr]
  generalize (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = U at hUm hsU hUs hs
  generalize hH.eigenvalues = ev at hs ⊢
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨U, star U, hsU, hUs⟩
  have hzH : z • H = (u : Matrix (Fin n) (Fin n) ℂ) *
      Matrix.diagonal (fun j => z * (ev j : ℂ)) * ((u⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
    show z • H = U * Matrix.diagonal (fun j => z * (ev j : ℂ)) * star U
    have hd : Matrix.diagonal (fun j => z * (ev j : ℂ)) = z • Matrix.diagonal (RCLike.ofReal ∘ ev) := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]
    rw [hd, Matrix.mul_smul, Matrix.smul_mul, hs]
  rw [hzH, Matrix.exp_units_conj, Matrix.det_mul, Matrix.det_mul, Matrix.exp_diagonal,
    Matrix.det_diagonal]
  have hdu : (u : Matrix (Fin n) (Fin n) ℂ).det * ((u⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  rw [Finset.mul_sum]
  simp only [Pi.exp_def, ← Complex.exp_eq_exp_ℂ]
  rw [Complex.exp_sum]
  calc _ = (u : Matrix (Fin n) (Fin n) ℂ).det * ((u⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ).det *
        ∏ j, Complex.exp (z * (ev j : ℂ)) := by ring
    _ = _ := by rw [hdu, one_mul]

lemma s38_det_exp (K : Matrix (Fin n) (Fin n) ℂ) (hK : Kᴴ = -K) (htr : K.trace = 0) (a : ℝ) :
    (NormedSpace.exp (a • K)).det = 1 := by
  have hH : ((-Complex.I) • K).IsHermitian := by
    show ((-Complex.I) • K)ᴴ = _
    rw [Matrix.conjTranspose_smul, hK]
    simp [Complex.conj_I]
  have hKH : (a : ℝ) • K = ((a : ℂ) * Complex.I) • ((-Complex.I) • K) := by
    rw [smul_smul, ← Complex.coe_smul]
    congr 1
    rw [mul_assoc]; simp
  rw [hKH, s38_det_exp_herm _ hH, Matrix.trace_smul, htr]
  simp

lemma s38_exp_ct (Ω : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    (NormedSpace.exp (t • Ω))ᴴ = NormedSpace.exp (t • Ωᴴ) := by
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul]
  simp

lemma s38_deriv1 (A C U Ω : Matrix (Fin n) (Fin n) ℂ) (hΩ : Ωᴴ = -Ω) :
    HasDerivAt (fun t : ℝ => Cᴴ * ((NormedSpace.exp (t • Ω) * U) * A *
          (NormedSpace.exp (t • Ω) * U)ᴴ))
      (Cᴴ * Ω * (U * A * Uᴴ) - Cᴴ * (U * A * Uᴴ) * Ω) 0 := by
  have hf : (fun t : ℝ => Cᴴ * ((NormedSpace.exp (t • Ω) * U) * A *
          (NormedSpace.exp (t • Ω) * U)ᴴ)) =
      fun t : ℝ => Cᴴ * ((NormedSpace.exp (t • Ω) * (U * A * Uᴴ)) * NormedSpace.exp (t • Ωᴴ)) := by
    funext t
    rw [Matrix.conjTranspose_mul, s38_exp_ct]
    simp only [Matrix.mul_assoc]
  rw [hf]
  have hg := hasDerivAt_exp_smul_const (𝕂 := ℝ) Ω (0 : ℝ)
  have hh := hasDerivAt_exp_smul_const (𝕂 := ℝ) Ωᴴ (0 : ℝ)
  have := ((hg.mul_const (U * A * Uᴴ)).mul hh).const_mul Cᴴ
  refine this.congr_deriv ?_
  simp only [zero_smul, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_one, hΩ]
  simp only [Matrix.mul_add, Matrix.mul_neg, Matrix.mul_assoc]
  abel

lemma s38_re_tr_hasDeriv {f : ℝ → Matrix (Fin n) (Fin n) ℂ} {D : Matrix (Fin n) (Fin n) ℂ}
    (hf : HasDerivAt f D 0) : HasDerivAt (fun t => (Matrix.trace (f t)).re) (Matrix.trace D).re 0 := by
  let φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℝ :=
    Complex.reLm.comp ((Matrix.traceLinearMap (Fin n) ℂ ℂ).restrictScalars ℝ)
  have := (LinearMap.toContinuousLinearMap φ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hf
  exact this


lemma s38_K_ct (X : Matrix (Fin n) (Fin n) ℂ) : (-skew X)ᴴ = -(-skew X) := by
  unfold skew
  rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose]
  simp only [star_inv₀, star_ofNat, neg_neg, smul_sub]
  rw [neg_sub]

lemma s38_K_special (M C : Matrix (Fin n) (Fin n) ℂ) : IsSpecialSkew (-skew (P38.comm M Cᴴ)) := by
  refine ⟨s38_K_ct _, ?_⟩
  unfold skew P38.comm
  rw [Matrix.trace_neg, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_conjTranspose,
    Matrix.trace_sub, Matrix.trace_mul_comm M]
  simp

lemma s38_pair (M C Ω : Matrix (Fin n) (Fin n) ℂ) (hΩ : Ωᴴ = -Ω) :
    (Matrix.trace (Cᴴ * Ω * M - Cᴴ * M * Ω)).re = realHSPairing (-skew (P38.comm M Cᴴ)) Ω := by
  unfold realHSPairing
  rw [s38_K_ct]
  set X := P38.comm M Cᴴ with hX
  have e1 : (Matrix.trace (Cᴴ * Ω * M - Cᴴ * M * Ω)) = (X * Ω).trace := by
    rw [hX]; unfold P38.comm
    rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_mul_cycle]
  have e2 : (Xᴴ * Ω).trace = - star ((X * Ω).trace) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hΩ, Matrix.neg_mul,
      Matrix.trace_neg, Matrix.trace_mul_comm]
    simp
  have e3 : (-(-skew X) * Ω).trace = (2 : ℂ)⁻¹ * ((X * Ω).trace - (Xᴴ * Ω).trace) := by
    unfold skew
    rw [neg_neg, Matrix.smul_mul, Matrix.trace_smul, Matrix.sub_mul, Matrix.trace_sub, smul_eq_mul]
  rw [e1, e3, e2]
  set w := (X * Ω).trace
  have : w - -star w = ((2 * w.re : ℝ) : ℂ) := by
    rw [sub_neg_eq_add, Complex.star_def, Complex.add_conj]
  rw [this]
  simp [Complex.mul_re]

end s38
theorem solution {n : ℕ} (hn : 0 < n) (A C : (Matrix (Fin n) (Fin n) ℂ))
    (U : Matrix.specialUnitaryGroup (Fin n) ℂ) :
    (∀ Omega : (Matrix (Fin n) (Fin n) ℂ), IsSpecialSkew Omega →
      HasDerivAt (fun t : ℝ => C.conjTranspose *
        ((NormedSpace.exp (t • Omega) * (U : (Matrix (Fin n) (Fin n) ℂ))) * A *
          (NormedSpace.exp (t • Omega) * (U : (Matrix (Fin n) (Fin n) ℂ))).conjTranspose))
        (C.conjTranspose * Omega * ((U : (Matrix (Fin n) (Fin n) ℂ)) * A * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose) -
          C.conjTranspose * ((U : (Matrix (Fin n) (Fin n) ℂ)) * A * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose) * Omega) 0) ∧
    IsSUGradient A C U (unitaryGradientField A C U) ∧
    (∀ V : (Matrix (Fin n) (Fin n) ℂ), IsSUGradient A C U V ↔ V = unitaryGradientField A C U) ∧
    (∀ a : ℝ, 0 ≤ a → unitaryAscentStep A C U a ∈ Matrix.specialUnitaryGroup (Fin n) ℂ) ∧
    HasDerivAt (unitaryAscentStep A C U) (unitaryGradientField A C U) 0 := by
  have hder : ∀ Ω : Matrix (Fin n) (Fin n) ℂ, IsSpecialSkew Ω → HasDerivAt (fun t : ℝ => C.conjTranspose *
        ((NormedSpace.exp (t • Ω) * (U : (Matrix (Fin n) (Fin n) ℂ))) * A *
          (NormedSpace.exp (t • Ω) * (U : (Matrix (Fin n) (Fin n) ℂ))).conjTranspose))
        (C.conjTranspose * Ω * ((U : (Matrix (Fin n) (Fin n) ℂ)) * A * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose) -
          C.conjTranspose * ((U : (Matrix (Fin n) (Fin n) ℂ)) * A * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose) * Ω) 0 :=
    fun Ω hΩ => s38_deriv1 A C _ Ω hΩ.1
  have hgrad : IsSUGradient A C U (unitaryGradientField A C U) := by
    refine ⟨-skew (P38.comm ((U : Matrix (Fin n) (Fin n) ℂ) * A * (U : Matrix (Fin n) (Fin n) ℂ)ᴴ) Cᴴ),
      s38_K_special _ _, rfl, fun Ω hΩ => ?_⟩
    have := s38_re_tr_hasDeriv (hder Ω hΩ)
    rw [s38_pair _ _ _ hΩ.1] at this
    exact this
  have hKs := s38_K_special ((U : Matrix (Fin n) (Fin n) ℂ) * A * (U : Matrix (Fin n) (Fin n) ℂ)ᴴ) C
  refine ⟨hder, hgrad, fun V => ⟨fun hV => ?_, fun h => h ▸ hgrad⟩, fun a _ => ?_, ?_⟩
  · obtain ⟨K', hK', rfl, hd'⟩ := hV
    obtain ⟨K, hK, hKe, hd⟩ := hgrad
    have hD : IsSpecialSkew (K' - K) := by
      refine ⟨?_, ?_⟩
      · rw [Matrix.conjTranspose_sub, hK'.1, hK.1]; abel
      · rw [Matrix.trace_sub, hK'.2, hK.2, sub_zero]
    have h1 := (hd' _ hD).unique (hd _ hD)
    have h2 : (Matrix.trace ((K' - K)ᴴ * (K' - K))).re = 0 := by
      unfold realHSPairing at h1
      rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, h1, sub_self]
    have hpsd := (Matrix.posSemidef_conjTranspose_mul_self (K' - K)).trace_nonneg
    have h3 : Matrix.trace ((K' - K)ᴴ * (K' - K)) = 0 := by
      apply Complex.ext
      · simpa using h2
      · simpa using ((Complex.nonneg_iff.mp hpsd).2).symm
    have h4 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h3
    rw [hKe, sub_eq_zero.mp h4]
  · unfold unitaryAscentStep
    refine Submonoid.mul_mem _ ?_ U.2
    generalize -skew (P38.comm ((U : Matrix (Fin n) (Fin n) ℂ) * A * (U : Matrix (Fin n) (Fin n) ℂ)ᴴ) Cᴴ) = K at hKs ⊢
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, s38_det_exp _ hKs.1 hKs.2 a⟩
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, s38_exp_ct, hKs.1,
      ← Matrix.exp_add_of_commute]
    · rw [smul_neg, add_neg_cancel, NormedSpace.exp_zero]
    · exact (((Commute.refl K).neg_right).smul_left a).smul_right a
  · unfold unitaryAscentStep unitaryGradientField
    generalize -skew (P38.comm ((U : Matrix (Fin n) (Fin n) ℂ) * A * (U : Matrix (Fin n) (Fin n) ℂ)ᴴ) Cᴴ) = K
    have := (hasDerivAt_exp_smul_const (𝕂 := ℝ) K (0 : ℝ)).mul_const (U : Matrix (Fin n) (Fin n) ℂ)
    refine this.congr_deriv ?_
    simp
