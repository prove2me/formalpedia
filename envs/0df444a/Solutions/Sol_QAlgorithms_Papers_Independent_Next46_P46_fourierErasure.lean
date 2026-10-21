-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P46.fourierErasure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T17:08:21.616952+00:00
-- url     : https://prove2.me/submissions/c9655398-e5fb-4098-97d4-bc41961223ab

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P46
noncomputable section

open QAlgorithms.Papers.Independent.Next46.P46

open QAlgorithms

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.decEq Classical.propDecidable

-- The repair request explicitly authorizes imports from the pinned accepted papers.

open QAlgorithms.Papers.Independent.Information100.P21 (Vec Op)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

open QAlgorithms.Papers.Independent.Frontier30.P12
  (coherentInfo quantumMutualInfo mutualAE marginalAE triCopies EntProtocol RectangularKrausData)

open QAlgorithms.Papers.Independent.Dependency50.P19 (channelSource)

open QAlgorithms.Papers.Independent.Dependency50.P48 (IsDilation)

lemma g62j_exp_conj (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) * (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I)) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  simp

lemma g62j_state_sum {H : Type} [Fintype H] (v : EuclideanSpace ℂ H) (hv : ‖v‖ = 1) :
    ∑ h, ‖v h‖ ^ 2 = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at hv
  exact hv

lemma g62j_erased_sq {H : Type} [Fintype H] {m s : ℕ} (hm : 0 < m) (hs : 0 < s)
    (phi : Fin m → Fin s → EuclideanSpace ℂ H)
    (hphi : ∀ a b, ‖phi a b‖ = 1) :
    ∑ z, ‖erasedVector phi z‖ ^ 2 = 1 := by
  have hz : ∀ z : (Fin m × (Fin m × Fin s)) × H, ‖erasedVector phi z‖ ^ 2 =
      if z.1.1 = z.1.2.1 then ((m : ℝ) * s)⁻¹ * ‖phi z.1.1 z.1.2.2 z.2‖ ^ 2 else 0 := by
    intro z
    split_ifs with h
    · simp only [erasedVector, PiLp.toLp_apply, h, if_true, norm_mul, mul_pow]
      congr 1
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
        Real.sq_sqrt (by positivity)]
    · simp [erasedVector, h]
  simp only [hz, Fintype.sum_prod_type]
  have : ∀ a : Fin m, (∑ a' : Fin m, ∑ j : Fin s, ∑ h : H,
      (if a = a' then ((m : ℝ) * s)⁻¹ * ‖phi a j h‖ ^ 2 else 0)) = ((m : ℝ) * s)⁻¹ * s := by
    intro a
    rw [Finset.sum_eq_single a]
    · simp only [if_true]
      simp_rw [← Finset.mul_sum, g62j_state_sum _ (hphi _ _)]
      simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  simp_rw [this]
  simp
  field_simp

/-- arXiv:quant-ph/0307053v1, PDF p.4: Fourier erasure on the displayed ideal state.
Each outcome has probability 1/S; after feed-forward every normalized branch is (5).
Residual vectors need only have unit norm, since the m,s labels are orthogonal. -/
theorem solution {H : Type} [Fintype H] [Nonempty H] {m s : ℕ}
    (hm : 0 < m) (hs : 0 < s) (phi : Fin m → Fin s → Vec H)
    (hphi : ∀ a b, IsState (phi a b)) :
    IsState (erasedVector phi) ∧
    (∀ t : Fin s, ‖fourierBranch phi t‖ ^ 2 = (s : ℝ)⁻¹ ∧
      correctedBranch phi t = ((Real.sqrt (s : ℝ))⁻¹ : ℂ) • erasedVector phi) ∧
    (∑ t : Fin s, pureDensity (correctedBranch phi t)) =
      pureDensity (erasedVector phi) := by
  have hE : ‖erasedVector phi‖ = 1 := by
    rw [EuclideanSpace.norm_eq, g62j_erased_sq hm hs phi hphi, Real.sqrt_one]
  have hB : ∀ t : Fin s, correctedBranch phi t = ((Real.sqrt (s : ℝ))⁻¹ : ℂ) • erasedVector phi := by
    intro t
    ext z
    simp only [correctedBranch, fourierBranch, erasedVector, fourierCoefficient, PiLp.toLp_apply,
      PiLp.smul_apply, smul_eq_mul]
    split_ifs with h
    · rw [map_mul]
      have := g62j_exp_conj (2 * Real.pi * (z.1.2.2 : ℝ) * (t : ℝ) / (s : ℝ))
      simp only [map_inv₀, Complex.conj_ofReal]
      linear_combination ((Real.sqrt (s : ℝ))⁻¹ : ℂ) * ((Real.sqrt ((m : ℝ) * s))⁻¹ : ℂ) * phi z.1.1 z.1.2.2 z.2 * this
    · simp
  have hC : ∀ t : Fin s, ‖fourierBranch phi t‖ = ‖correctedBranch phi t‖ := by
    intro t
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl (fun z _ => ?_)
    simp only [correctedBranch, PiLp.toLp_apply, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  refine ⟨hE, fun t => ⟨?_, hB t⟩, ?_⟩
  · rw [hC, hB, norm_smul, hE, mul_one, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (by positivity)]
  · simp_rw [hB]
    ext a b
    simp only [pureDensity, Matrix.sum_apply, Matrix.of_apply, PiLp.smul_apply, smul_eq_mul, map_mul,
      map_inv₀, Complex.conj_ofReal, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hs' : (Real.sqrt (s : ℝ) : ℂ) ^ 2 = s := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; simp
    have hs0 : (Real.sqrt (s : ℝ) : ℂ) ≠ 0 := by
      simp; omega
    field_simp
    rw [hs']



end
