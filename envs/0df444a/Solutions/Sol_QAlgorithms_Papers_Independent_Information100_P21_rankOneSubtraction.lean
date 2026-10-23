-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P21.rankOneSubtraction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:41:32.993661+00:00
-- url     : https://prove2.me/submissions/6d4d11c9-ef34-4496-80f9-3c312e30ba07

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X6RankOne

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P21

lemma posSemidef_of_forall {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (h : ∀ v : ι → ℂ, 0 ≤ star v ⬝ᵥ (M *ᵥ v)) : M.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ h
  rw [← Matrix.isSymmetric_toEuclideanLin_iff, LinearMap.isSymmetric_iff_inner_map_self_real]
  intro v
  have hz := h v.ofLp
  have hre : (star v.ofLp ⬝ᵥ (M *ᵥ v.ofLp)).im = 0 := (Complex.nonneg_iff.mp hz).2.symm
  have hin : inner ℂ (M.toEuclideanLin v) v = conj (star v.ofLp ⬝ᵥ (M *ᵥ v.ofLp)) := by
    rw [← inner_conj_symm, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin_apply,
      dotProduct_comm]
  rw [hin, Complex.conj_conj]
  apply Complex.ext <;> simp [hre]

lemma quad_eq {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    quad M v = (star (fun i => v i) ⬝ᵥ (M *ᵥ fun i => v i)).re := by
  unfold quad
  congr 1
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def,
    mul_assoc]

lemma re_of_nonneg {z : ℂ} (h : 0 ≤ z) : z = (z.re : ℂ) :=
  Complex.ext rfl (by simp [(Complex.nonneg_iff.mp h).2.symm])

lemma cs {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    Complex.normSq (star a ⬝ᵥ b) ≤ (star a ⬝ᵥ a).re * (star b ⬝ᵥ b).re := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 b) (WithLp.toLp 2 a)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  have e : a ⬝ᵥ star b = star (star a ⬝ᵥ b) := by simp [dotProduct, mul_comm]
  simp only [WithLp.ofLp_toLp] at h
  rw [e, norm_star] at h
  have ha : ‖(WithLp.toLp 2 a : EuclideanSpace ℂ ι)‖ ^ 2 = (star a ⬝ᵥ a).re := by
    rw [← @inner_self_eq_norm_sq ℂ, EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct_comm]
  have hb : ‖(WithLp.toLp 2 b : EuclideanSpace ℂ ι)‖ ^ 2 = (star b ⬝ᵥ b).re := by
    rw [← @inner_self_eq_norm_sq ℂ, EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct_comm]
  rw [Complex.normSq_eq_norm_sq, ← ha, ← hb, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (by linarith [h]) 2

end X6RankOne

open X6RankOne in
open QAlgorithms.Papers.Independent.Information100.P21 in
theorem solution (W : Op QQ) (hW : W.PosSemidef) (p : Vec QQ) (hp : ‖p‖=1)
  (hr : (fun i => p i) ∈ LinearMap.range (Matrix.toLin' W)) :
  0 < quad (pseudo W) p ∧ 0 < (quad (pseudo W) p)⁻¹ ∧
    (W - ((quad (pseudo W) p)⁻¹:ℂ) • proj p).PosSemidef ∧
    Matrix.rank (W - ((quad (pseudo W) p)⁻¹:ℂ) • proj p) < Matrix.rank W := by
  obtain ⟨y, hy⟩ := hr
  rw [Matrix.toLin'_apply] at hy
  set pv : QQ → ℂ := fun i => p i with hpv
  -- square root
  open scoped MatrixOrder in
  have h0 : 0 ≤ W := Matrix.nonneg_iff_posSemidef.mpr hW
  set S := CFC.sqrt W with hSdef
  open scoped MatrixOrder in
  have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg W)
  have hSS : W = S * S := (CFC.sqrt_mul_sqrt_self W h0).symm
  have hSh : Sᴴ = S := hS.isHermitian.eq
  have hWh : Wᴴ = W := hW.isHermitian.eq
  have form : ∀ u v : QQ → ℂ, star u ⬝ᵥ (W *ᵥ v) = star (S *ᵥ u) ⬝ᵥ (S *ᵥ v) := by
    intro u v
    rw [hSS, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec, hSh]
  -- pseudo inverse identity
  have hWW : W * pseudo W * W = W := by
    unfold pseudo
    have hsa : IsSelfAdjoint W := hW.isHermitian
    have hfin : (spectrum ℝ W).Finite := Matrix.finite_real_spectrum
    have e1 := cfc_mul (fun x : ℝ => x) (fun x : ℝ => x⁻¹) W (hfin.continuousOn _)
      (hfin.continuousOn _)
    have e2 := cfc_mul (fun x : ℝ => x * x⁻¹) (fun x : ℝ => x) W (hfin.continuousOn _)
      (hfin.continuousOn _)
    rw [cfc_id' ℝ W] at e1 e2
    rw [← e1, ← e2]
    conv_rhs => rw [← cfc_id' ℝ W]
    congr 1
    funext x
    by_cases hx : x = 0
    · simp [hx]
    · field_simp
  set γ := star y ⬝ᵥ (W *ᵥ y) with hγ
  have hγn : 0 ≤ γ := by rw [hγ, form]; exact dotProduct_star_self_nonneg _
  have hquad : quad (pseudo W) p = γ.re := by
    rw [quad_eq, ← hpv, ← hy, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hWh, hWW]
  have hpne : pv ≠ 0 := by
    intro h
    apply one_ne_zero (α := ℝ)
    rw [← hp]
    have : p = 0 := by
      ext i; have := congrFun h i; simpa [hpv] using this
    simp [this]
  have hcpos : 0 < γ.re := by
    rcases (Complex.nonneg_iff.mp hγn).1.lt_or_eq with h | h
    · exact h
    · exfalso
      have hz : γ = 0 := by rw [re_of_nonneg hγn, ← h]; simp
      rw [hγ, form, dotProduct_star_self_eq_zero] at hz
      apply hpne
      rw [← hy, hSS, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
  rw [hquad]
  set c := γ.re with hc
  have hγc : γ = (c : ℂ) := re_of_nonneg hγn
  -- action of proj p
  have hproj : ∀ v : QQ → ℂ, proj p *ᵥ v = (star pv ⬝ᵥ v) • pv := by
    intro v; ext i
    simp only [proj, QAlgorithms.pureDensity, Matrix.mulVec, dotProduct, Matrix.of_apply,
      Pi.smul_apply, smul_eq_mul, Pi.star_apply, RCLike.star_def, hpv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hpy : star pv ⬝ᵥ y = (c : ℂ) := by
    rw [← hy, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hWh, ← hγc]
  refine ⟨hcpos, inv_pos.mpr hcpos, ?_, ?_⟩
  · refine posSemidef_of_forall _ fun v => ?_
    set z := star v ⬝ᵥ pv with hz
    have hzc : star pv ⬝ᵥ v = conj z := by
      rw [hz]; simp [dotProduct, map_sum, mul_comm]
    have hpvS : z = star (S *ᵥ v) ⬝ᵥ (S *ᵥ y) := by rw [hz, ← hy, form]
    have hX := dotProduct_star_self_nonneg (S *ᵥ v)
    set X := star (S *ᵥ v) ⬝ᵥ (S *ᵥ v) with hXdef
    have hcs := cs (S *ᵥ v) (S *ᵥ y)
    rw [← hpvS, ← form y y, ← hγ, ← hXdef] at hcs
    have key : star v ⬝ᵥ ((W - ((c : ℂ))⁻¹ • proj p) *ᵥ v) =
        ((X.re - c⁻¹ * Complex.normSq z : ℝ) : ℂ) := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hproj, dotProduct_sub, dotProduct_smul,
        dotProduct_smul, form, ← hXdef, hzc, ← hz, re_of_nonneg hX]
      push_cast
      rw [Complex.normSq_eq_conj_mul_self]
      simp only [smul_eq_mul, Complex.ofReal_re]
      try ring
    rw [key]
    have : c⁻¹ * Complex.normSq z ≤ X.re := by
      rw [inv_mul_le_iff₀ hcpos]; linarith
    exact_mod_cast sub_nonneg.mpr this
  · set W' := W - ((c : ℂ))⁻¹ • proj p with hW'
    have hk : LinearMap.ker W.mulVecLin < LinearMap.ker W'.mulVecLin := by
      rw [SetLike.lt_iff_le_and_exists]
      refine ⟨fun v hv => ?_, y, ?_, ?_⟩
      · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
        have : star pv ⬝ᵥ v = 0 := by
          rw [← hy, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hWh, hv, dotProduct_zero]
        rw [hW', Matrix.sub_mulVec, Matrix.smul_mulVec, hproj, this, hv]; simp
      · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hW', Matrix.sub_mulVec,
          Matrix.smul_mulVec, hproj, hpy, hy, smul_smul]
        have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
        push_cast
        rw [inv_mul_cancel₀ hc0, one_smul, sub_self]
      · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hy]; exact hpne
    have h1 := LinearMap.finrank_range_add_finrank_ker W.mulVecLin
    have h2 := LinearMap.finrank_range_add_finrank_ker W'.mulVecLin
    have h3 := Submodule.finrank_lt_finrank_of_lt hk
    unfold Matrix.rank
    omega
