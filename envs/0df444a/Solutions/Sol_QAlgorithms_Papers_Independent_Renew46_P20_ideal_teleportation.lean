-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P20.ideal_teleportation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T01:32:48.56385+00:00
-- url     : https://prove2.me/submissions/b8af35fc-327f-4eb5-9a30-8dee271c622f

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P20
noncomputable section

open MeasureTheory

open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P40 (operatorKet)

open QAlgorithms.Papers.Independent.Renew46.P20
open QAlgorithms

theorem g65b_tele {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (U rho : Matrix I I ℂ) :
    teleportRaw (idealResource I) (bellEffectDensity U) rho = Uᴴ * rho * U := by
  ext b c
  have hd : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [teleportRaw, traceAlice, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, aliceLift,
    idealResource, bellEffectDensity, pureDensity, operatorKet, Matrix.smul_apply, Matrix.of_apply,
    Matrix.one_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, smul_eq_mul,
    Fintype.sum_prod_type]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_one, map_zero, mul_one, one_mul]
  simp only [apply_ite (starRingEnd ℂ), map_one, map_zero, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, mul_one]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  field_simp
  simp [Complex.star_def]

theorem g65b_pd_psd {n : Type*} [Fintype n] (a : EuclideanSpace ℂ n) :
    (QAlgorithms.pureDensity a).PosSemidef := by
  have : QAlgorithms.pureDensity a = Matrix.vecMulVec (WithLp.ofLp a) (star (WithLp.ofLp a)) := by
    ext i j; simp [QAlgorithms.pureDensity, Matrix.vecMulVec_apply]
  rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _

def g65b_L (I : Type*) [Fintype I] : Matrix (I × I) (I × I) ℂ →L[ℂ] Matrix (I × I) (I × I) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (Fintype.card I : ℂ) • M.submatrix Prod.swap Prod.swap
      map_add' := by intro A B; ext; simp [mul_add]
      map_smul' := by intro r A; ext; simp; ring }

theorem g65b_L_apply {I : Type*} [Fintype I] (U : Matrix I I ℂ) :
    g65b_L I (pureDensity (operatorKet U)) = bellEffectDensity U := by
  ext p q
  simp [g65b_L, bellEffectDensity, pureDensity, operatorKet]

/-- PDF p.20, §7.0.1, Eq.(98), with an explicit source normalization correction.
Printed: Eq.(83), p.17, has frame integral I tensor I (unitary-frame measure mass d),
while p.19 infers K = I/d and Eqs.(93)–(98) use the Bell density d |U^T><U^T|.
Changed: the reference measure is a probability measure and the frame integral is
I tensor I / d; the resource and contraction of Eq.(98) are unchanged.
Why: partial trace of Eq.(84) gives K = mu(Omega) I/d for a unitary family.
Dividing the Eq.(83) measure by d normalizes the Bell POVM in Eq.(98).
The shared state and Bell effects are computed from the frame; a normalized
measurable POVM on the same outcome space is a conclusion. The historical
classification assertion attributed to [28–30] is not claimed. -/
theorem solution
    {I W : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [MeasurableSpace W]
    (mu : Measure W) [IsProbabilityMeasure mu]
    (U : W → Matrix.unitaryGroup I ℂ)
    (hU : StronglyMeasurable (fun w => (U w : Matrix I I ℂ)))
    (hframe : Integrable (fun w => pureDensity
      (operatorKet (U w : Matrix I I ℂ))) mu)
    (htight : (∫ w, pureDensity (operatorKet (U w : Matrix I I ℂ)) ∂mu) =
      (Fintype.card I : ℂ)⁻¹ • (1 : Matrix (I × I) (I × I) ℂ)) :
    IsDensityMatrix (idealResource I) ∧
    (∃ D : Measurements.DensityPOVM (I × I) W,
      D.reference = mu ∧ D.density = (fun w => bellEffectDensity (U w : Matrix I I ℂ))) ∧
    ∀ (rho : Matrix I I ℂ), IsDensityMatrix rho → ∀ w,
      (U w : Matrix I I ℂ) *
        teleportRaw (idealResource I) (bellEffectDensity (U w : Matrix I I ℂ)) rho *
        (U w : Matrix I I ℂ)ᴴ = rho := by
  have hd : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · unfold idealResource
    exact (g65b_pd_psd _).smul (by
      rw [inv_nonneg]; exact_mod_cast Nat.zero_le _)
  · simp only [idealResource, Matrix.trace_smul, Matrix.trace, pureDensity, operatorKet,
      Matrix.of_apply, Matrix.one_apply, Fintype.sum_prod_type, smul_eq_mul, Matrix.diag_apply, Matrix.smul_apply]
    simp only [apply_ite (starRingEnd ℂ), map_one, map_zero, mul_ite, mul_zero, mul_one,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  · have hint : Integrable (fun w => bellEffectDensity (U w : Matrix I I ℂ)) mu := by
      have := (g65b_L I).integrable_comp hframe
      simpa [g65b_L_apply] using this
    have hmeas : StronglyMeasurable (fun w => bellEffectDensity (U w : Matrix I I ℂ)) := by
      have hc : Continuous (fun M : Matrix I I ℂ => bellEffectDensity M) := by
        have : (fun M : Matrix I I ℂ => bellEffectDensity M) =
            fun M => g65b_L I (pureDensity (operatorKet M)) := by
          funext M; rw [g65b_L_apply]
        rw [this]
        refine (g65b_L I).continuous.comp ?_
        refine continuous_pi fun a => continuous_pi fun b => ?_
        simp only [pureDensity, operatorKet, Matrix.of_apply]
        have h1 : Continuous (fun M : Matrix I I ℂ => M a.1 a.2) :=
          (continuous_apply a.2).comp (continuous_apply a.1)
        have h2 : Continuous (fun M : Matrix I I ℂ => M b.1 b.2) :=
          (continuous_apply b.2).comp (continuous_apply b.1)
        exact h1.mul (Complex.continuous_conj.comp h2)
      exact hc.comp_stronglyMeasurable hU
    refine ⟨⟨mu, inferInstance, fun w => bellEffectDensity (U w : Matrix I I ℂ),
      ?_, ?_, hint, ?_⟩, rfl, rfl⟩
    · letI : MeasurableSpace (Matrix (I × I) (I × I) ℂ) := borel _
      haveI : BorelSpace (Matrix (I × I) (I × I) ℂ) := ⟨rfl⟩
      exact hmeas.measurable
    · intro w
      exact (g65b_pd_psd _).smul (by exact_mod_cast Nat.zero_le _)
    · have := (g65b_L I).integral_comp_comm hframe
      simp only [g65b_L_apply] at this
      rw [this, htight]
      ext p q
      simp [g65b_L, Matrix.one_apply, Prod.swap_inj]
  · intro rho _ w
    rw [g65b_tele]
    have h1 : (U w : Matrix I I ℂ) * (U w : Matrix I I ℂ)ᴴ = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (U w).2
    calc (U w : Matrix I I ℂ) * ((U w : Matrix I I ℂ)ᴴ * rho * (U w : Matrix I I ℂ)) *
          (U w : Matrix I I ℂ)ᴴ
        = ((U w : Matrix I I ℂ) * (U w : Matrix I I ℂ)ᴴ) * rho *
          ((U w : Matrix I I ℂ) * (U w : Matrix I I ℂ)ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = rho := by rw [h1, Matrix.one_mul, Matrix.mul_one]



end
