-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P24.jones_propagation_contracting
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-20T15:04:47.855367+00:00
-- url     : https://prove2.me/submissions/67cef735-0a19-4fc8-84d6-ee4ec31f294a

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P24
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder Matrix.Norms.L2Operator

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P49 (traceDual)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

namespace QAlgorithms.Papers.Independent.Intake100.P24

local instance : MeasurableSpace PolarizationMatrix := borel PolarizationMatrix

local instance : BorelSpace PolarizationMatrix := ⟨rfl⟩

theorem _root_.solution
    (omega gamma gammaDec : PolarizationMatrix) (homega : omega.IsHermitian)
    (hgamma : gamma.PosSemidef) (hdec : gammaDec.PosSemidef)
    (t : ℝ) (ht : 0 ≤ t) :
    (1 - jonesPropagation omega gamma gammaDec t *
      (jonesPropagation omega gamma gammaDec t)ᴴ).PosSemidef := by
  set K : PolarizationMatrix := Complex.I • omega + (1 / 2 : ℂ) • gamma + gammaDec with hK
  have hKs : K + Kᴴ = gamma + (2 : ℂ) • gammaDec := by
    have h1 : omegaᴴ = omega := homega
    have h2 : gammaᴴ = gamma := hgamma.isHermitian
    have h3 : gammaDecᴴ = gammaDec := hdec.isHermitian
    rw [hK, Matrix.conjTranspose_add, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_smul, h1, h2, h3]
    have : star Complex.I = -Complex.I := Complex.conj_I
    rw [this]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, neg_mul]
    ring
  have hKpsd : (K + Kᴴ).PosSemidef := by
    rw [hKs]; exact hgamma.add (hdec.smul (by norm_num))
  have hV : ∀ s : ℝ, jonesPropagation omega gamma gammaDec s = NormedSpace.exp (s • (-K)) := by
    intro s
    unfold jonesPropagation
    congr 1
    rw [smul_neg, neg_smul]
    congr 1
  have hVh : ∀ s : ℝ, (jonesPropagation omega gamma gammaDec s)ᴴ = NormedSpace.exp (s • (-Kᴴ)) := by
    intro s
    rw [hV, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, Matrix.conjTranspose_neg]
    simp
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨Matrix.isHermitian_one.sub (Matrix.isHermitian_mul_conjTranspose_self _), fun x => ?_⟩
  set Q : ℝ → PolarizationMatrix := fun s =>
    NormedSpace.exp (s • (-K)) * NormedSpace.exp (s • (-Kᴴ)) with hQ
  let L : PolarizationMatrix →ₗ[ℝ] ℝ :=
    { toFun := fun M => (star x ⬝ᵥ (M *ᵥ x)).re
      map_add' := by intro M N; simp only [Matrix.add_mulVec, dotProduct_add, Complex.add_re]
      map_smul' := by
        intro r M
        first
          | simp only [Matrix.smul_mulVec_assoc, dotProduct_smul, Complex.smul_re, smul_eq_mul, RingHom.id_apply]
          | simp only [Matrix.smul_mulVec, dotProduct_smul, Complex.smul_re, smul_eq_mul, RingHom.id_apply] }
  let Lc : PolarizationMatrix →L[ℝ] ℝ := LinearMap.toContinuousLinearMap L
  have hd : ∀ s : ℝ, HasDerivAt (fun s => Lc (Q s))
      (Lc (NormedSpace.exp (s • (-K)) * (-K) * NormedSpace.exp (s • (-Kᴴ)) +
        NormedSpace.exp (s • (-K)) * ((-Kᴴ) * NormedSpace.exp (s • (-Kᴴ))))) s := by
    intro s
    have e1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-K) s
    have e2 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-Kᴴ) s
    exact Lc.hasFDerivAt.comp_hasDerivAt s (e1.mul e2)
  have hneg : ∀ s : ℝ, Lc (NormedSpace.exp (s • (-K)) * (-K) * NormedSpace.exp (s • (-Kᴴ)) +
        NormedSpace.exp (s • (-K)) * ((-Kᴴ) * NormedSpace.exp (s • (-Kᴴ)))) ≤ 0 := by
    intro s
    have hE : (NormedSpace.exp (s • (-K)))ᴴ = NormedSpace.exp (s • (-Kᴴ)) := by
      rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, Matrix.conjTranspose_neg]; simp
    have heq : NormedSpace.exp (s • (-K)) * (-K) * NormedSpace.exp (s • (-Kᴴ)) +
        NormedSpace.exp (s • (-K)) * ((-Kᴴ) * NormedSpace.exp (s • (-Kᴴ))) =
        -(NormedSpace.exp (s • (-K)) * (K + Kᴴ) * (NormedSpace.exp (s • (-K)))ᴴ) := by
      rw [hE]; noncomm_ring
    have hp := (hKpsd.mul_mul_conjTranspose_same (NormedSpace.exp (s • (-K)))).re_dotProduct_nonneg x
    rw [heq]
    show (star x ⬝ᵥ ((-_) *ᵥ x)).re ≤ 0
    rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]
    exact neg_nonpos.mpr hp
  have hanti : Antitone (fun s => Lc (Q s)) := antitone_of_hasDerivAt_nonpos hd hneg
  have hle := hanti ht
  have hQ0 : Q 0 = 1 := by simp [hQ]
  have hQt : Q t = jonesPropagation omega gamma gammaDec t *
      (jonesPropagation omega gamma gammaDec t)ᴴ := by rw [hVh, hV]
  have hherm : (1 - jonesPropagation omega gamma gammaDec t *
      (jonesPropagation omega gamma gammaDec t)ᴴ).IsHermitian :=
    Matrix.isHermitian_one.sub (Matrix.isHermitian_mul_conjTranspose_self _)
  have him := hherm.im_star_dotProduct_mulVec_self x
  rw [Complex.nonneg_iff]
  refine ⟨?_, ?_⟩
  · simp only [Lc, L, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk] at hle
    rw [hQ0, hQt] at hle
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
    simp only [Matrix.one_mulVec] at hle ⊢
    show (0:ℝ) ≤ _
    linarith
  · simpa [eq_comm] using him

end QAlgorithms.Papers.Independent.Intake100.P24

end
