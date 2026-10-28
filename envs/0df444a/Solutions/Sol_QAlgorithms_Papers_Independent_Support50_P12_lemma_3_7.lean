-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P12.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:10:47.328701+00:00
-- url     : https://prove2.me/submissions/572b9383-b8ce-44b6-b6d5-27451089e526

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12
noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

open scoped MatrixOrder

theorem S169_tr_eq (Phi : MatrixMap I J) (hH : (channelAdjoint Phi 1)ᴴ = channelAdjoint Phi 1)
    (X : Mat I) : (Phi X).trace = (channelAdjoint Phi 1 * X).trace := by
  set M := channelAdjoint Phi 1 with hM
  have hMij : ∀ i j, M j i = (Phi (Matrix.single i j 1)).trace := by
    intro i j
    have h1 : M j i = star (M i j) := by
      conv_lhs => rw [← hH]
      rfl
    rw [h1, hM]
    simp only [channelAdjoint, Matrix.one_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.trace, star_sum]
    simp
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, map_smul, Matrix.trace_sum, Matrix.trace_smul]
  rw [Matrix.trace]
  simp only [Matrix.mul_apply, Matrix.diag]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hMij, show Matrix.single j i (X j i) = X j i • Matrix.single j i (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, Matrix.trace_smul, smul_eq_mul, mul_comm]

theorem S169_main [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (Phi : MatrixMap I J)
    (hp : Substochastic A B Phi) (X : Mat I) (hX : X ∈ A) (hXp : X.PosSemidef)
    (hn : X ≠ 0) (ht : tr (Phi X) = tr X) :
    snorm B (channelAdjoint Phi) = 1 ∧ pnorm (channelAdjoint Phi) = 1 := by
  set M := channelAdjoint Phi 1 with hM
  have h1B : (1 : Mat J) ∈ B := B.one_mem
  have hMpos : M.PosSemidef := hp.2.2.1 1 h1B Matrix.PosSemidef.one
  have hMH : Mᴴ = M := hMpos.1
  have hsch : (M - Mᴴ * M).PosSemidef := by
    have := hp.2.2.2 1 h1B
    simpa [QAlgorithms.Papers.Independent.Dependency50.P28.LE] using this
  have hsch' : (M - M * M).PosSemidef := by rwa [hMH] at hsch
  have h1M : (1 - M).PosSemidef := by
    have e : 1 - M = (1 - M)ᴴ * (1 - M) + (M - M * M) := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hMH]; noncomm_ring
    rw [e]; exact (Matrix.posSemidef_conjTranspose_mul_self _).add hsch'
  have h1MM : (1 - Mᴴ * M).PosSemidef := by
    have e : 1 - Mᴴ * M = (1 - M) + (M - M * M) := by rw [hMH]; noncomm_ring
    rw [e]; exact h1M.add hsch'
  -- trace identity
  have htr : (Phi X).trace = (M * X).trace := S169_tr_eq Phi hMH X
  have hre : ((1 - M) * X).trace.re = 0 := by
    have : tr (Phi X) = tr X := ht
    simp only [tr] at this
    rw [htr] at this
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, this, sub_self]
  -- (1 - M) X = 0
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h1M.nonneg
  obtain ⟨D, hD⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hXp.nonneg
  have hPX : (1 - M) * X = 0 := by
    set E := C * star D
    have htE : ((1 - M) * X).trace = (Eᴴ * E).trace := by
      rw [hC, hD]
      simp only [E, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
      rw [show Cᴴ * C * (Dᴴ * D) = (Cᴴ * C * Dᴴ) * D by noncomm_ring, Matrix.trace_mul_comm]
      congr 1; noncomm_ring
    have hnn : 0 ≤ (Eᴴ * E).trace := (Matrix.posSemidef_conjTranspose_mul_self E).trace_nonneg
    have hz : (Eᴴ * E).trace = 0 := by
      rw [← htE] at hnn ⊢
      apply Complex.ext
      · simpa using hre
      · simpa using (Complex.nonneg_iff.mp hnn).2.symm
    rw [Matrix.trace_conjTranspose_mul_self_eq_zero_iff] at hz
    rw [hC, hD]
    simp only [Matrix.star_eq_conjTranspose] at hz ⊢
    rw [show Cᴴ * C * (Dᴴ * D) = Cᴴ * (C * Dᴴ) * D by noncomm_ring]
    change Cᴴ * E * D = 0
    rw [hz]; simp
  -- eigenvector
  obtain ⟨j0, hj0⟩ : ∃ j, (fun i => X i j) ≠ 0 := by
    by_contra h; push Not at h
    exact hn (Matrix.ext fun i j => congrFun (h j) i)
  set x : I → ℂ := fun i => X i j0
  have hMx : M *ᵥ x = x := by
    have : ((1 - M) * X) *ᵥ Pi.single j0 1 = 0 := by rw [hPX]; exact Matrix.zero_mulVec _
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec] at this
    have hx : X *ᵥ Pi.single j0 1 = x := by
      ext i; simp [x, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hx] at this
    exact (sub_eq_zero.mp this).symm
  set s : ℝ := ∑ i, ‖x i‖ ^ 2 with hs
  have hspos : 0 < s := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h; push Not at h; exact hj0 (funext h)
    have : 0 < ‖x i‖ ^ 2 := by positivity
    exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ i))
  set u : I → ℂ := ((Real.sqrt s)⁻¹ : ℂ) • x with hu
  have hMu : M *ᵥ u = u := by rw [hu, Matrix.mulVec_smul, hMx]
  have hnorm : ∑ i, ‖u i‖ ^ 2 = 1 := by
    simp only [hu, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum, ← hs]
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      inv_pow, Real.sq_sqrt hspos.le, inv_mul_cancel₀ hspos.ne']
  have hdot : ∀ v : I → ℂ, star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.ofReal_sum,
      Complex.ofReal_pow]
  have huu : star u ⬝ᵥ u = 1 := by rw [hdot, hnorm]; simp
  have hMMu : (Mᴴ * M) *ᵥ u = u := by rw [← Matrix.mulVec_mulVec, hMu, hMH, hMu]
  constructor
  · -- snorm
    apply IsLeast.csInf_eq
    refine ⟨⟨1, hp.2, by simp⟩, ?_⟩
    rintro c ⟨r, hr, rfl⟩
    have h := hr.2.2 1 h1B
    simp only [QAlgorithms.Papers.Independent.Dependency50.P28.LE, Matrix.conjTranspose_one, Matrix.one_mul] at h
    have h2 := h.dotProduct_mulVec_nonneg u
    rw [Matrix.sub_mulVec, dotProduct_sub, hMMu, Matrix.smul_mulVec, ← hM, hMu, dotProduct_smul,
      huu, smul_eq_mul, mul_one] at h2
    have h3 : (0:ℝ) ≤ r - 1 := by
      have := (Complex.nonneg_iff.mp h2).1
      simpa using this
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · -- pnorm
    unfold pnorm
    rw [← hM]
    have hS : sSup {x : ℝ | ∃ v : I → ℂ, ∑ j, ‖v j‖ ^ 2 = 1 ∧
        x = (∑ j, conj (v j) * ((Mᴴ * M) *ᵥ v) j).re} = 1 := by
      apply IsGreatest.csSup_eq
      refine ⟨⟨u, hnorm, ?_⟩, ?_⟩
      · have : (∑ j, conj (u j) * ((Mᴴ * M) *ᵥ u) j) = star u ⬝ᵥ ((Mᴴ * M) *ᵥ u) := rfl
        rw [this, hMMu, huu]; simp
      · rintro y ⟨v, hv, rfl⟩
        have h2 := h1MM.dotProduct_mulVec_nonneg v
        rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, hdot, hv] at h2
        have := (Complex.nonneg_iff.mp h2).1
        have e : (∑ j, conj (v j) * ((Mᴴ * M) *ᵥ v) j) = star v ⬝ᵥ ((Mᴴ * M) *ᵥ v) := rfl
        rw [e]
        simp only [Complex.sub_re, Complex.ofReal_one, Complex.one_re, Complex.zero_re] at this
        linarith
    rw [hS, Real.sqrt_one]

end QAlgorithms.Papers.Independent.Support50.P12

end

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Support50.P12
open QAlgorithms.Papers.Independent.Information100.P60 (Mat)
open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)
open QAlgorithms.Papers.Independent.Dependency50.P28 (tr)
open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)

theorem solution {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (Phi : MatrixMap I J)
    (hp : Substochastic A B Phi) (X : Mat I) (hX : X ∈ A) (hXp : X.PosSemidef)
    (hn : X ≠ 0) (ht : tr (Phi X) = tr X) :
    snorm B (channelAdjoint Phi) = 1 ∧ pnorm (channelAdjoint Phi) = 1 :=
  S169_main A B Phi hp X hX hXp hn ht
