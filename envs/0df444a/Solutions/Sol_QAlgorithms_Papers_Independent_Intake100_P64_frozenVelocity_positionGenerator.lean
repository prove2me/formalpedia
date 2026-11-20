-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P64.frozenVelocity_positionGenerator
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T10:38:43.92269+00:00
-- url     : https://prove2.me/submissions/eac4c24f-2d53-4a21-81d4-a935f29cd365

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

theorem AuxCDR_normSq (d : CollisionData) (p P Q : Momentum) :
    Complex.normSq (collisionCoefficient d p P Q) =
      prefactor d.parameters Q * d.gas.value (gasArgument d.parameters p P Q) *
        crossSection d (transverseRelative d.parameters p P Q - (1 / 2 : ℝ) • Q)
          (transverseRelative d.parameters p P Q + (1 / 2 : ℝ) • Q) := by
  unfold collisionCoefficient
  by_cases hQ : Q = 0
  · simp [hQ, prefactor]
  · have hpre : 0 ≤ prefactor d.parameters Q := by
      unfold prefactor
      rw [if_neg hQ]
      have := d.parameters.density_pos
      have := d.parameters.m_pos
      positivity
    have hg := d.gas.nonnegative (gasArgument d.parameters p P Q)
    rw [if_neg hQ, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
      Complex.normSq_ofReal, crossSection]
    rw [Real.mul_self_sqrt hpre, Real.mul_self_sqrt hg]
    ring


theorem _root_.solution (d : CollisionData) (F : TransverseFrames)
    (P0 : Momentum) (hGamma : 0 < collisionLossRate d F P0)
    (hplane : ∀ᵐ Q : Momentum, Integrable (rateIntegrand d F P0 Q))
    (hloss : Integrable (outgoingIntensity d F P0)) (r : MomentumKernel) :
    (∫ Q, transferRate d F P0 Q / collisionLossRate d F P0) = 1 ∧
    frozenCharacteristic d F P0 0 = 1 ∧
    (∀ X Xprime, frozenPositionGenerator d F P0 r X Xprime =
      -(collisionLossRate d F P0 : ℂ) * (1 - frozenCharacteristic d F P0 (X - Xprime)) * r X Xprime) := by
  have hT : ∀ Q, transferRate d F P0 Q = outgoingIntensity d F P0 Q := by
    intro Q; unfold transferRate outgoingIntensity
    congr 1; funext k; rw [AuxCDR_normSq]; rfl
  have hTi : Integrable (fun Q => transferRate d F P0 Q) := by
    simpa only [hT] using hloss
  have hL : collisionLossRate d F P0 = ∫ Q, transferRate d F P0 Q := by
    unfold collisionLossRate; simp only [hT]
  set Γ := collisionLossRate d F P0 with hΓ
  have hΓ0 : Γ ≠ 0 := hGamma.ne'
  have h1 : (∫ Q, transferRate d F P0 Q / Γ) = 1 := by
    rw [integral_div, ← hL, div_self hΓ0]
  refine ⟨h1, ?_, ?_⟩
  · unfold frozenCharacteristic
    have : ∀ Q : Momentum, momentumDot Q 0 = 0 := fun Q => by simp [momentumDot]
    simp only [this, zero_div, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    rw [integral_complex_ofReal, ← hΓ, h1, Complex.ofReal_one]
  · intro X Xprime
    set E : Momentum → ℂ := fun Q =>
      Complex.exp (Complex.I * (momentumDot Q (X - Xprime) / d.parameters.hbar : ℝ)) with hE
    have hEm : Continuous E := by
      simp only [hE, momentumDot]; fun_prop
    have hEb : ∀ Q, ‖E Q‖ ≤ 1 := by
      intro Q; simp only [hE]
      rw [Complex.norm_exp]; simp
    have hTE : Integrable (fun Q => (transferRate d F P0 Q : ℂ) * E Q) :=
      hTi.ofReal.mul_bdd hEm.aestronglyMeasurable (ae_of_all _ hEb)
    have hphi : frozenCharacteristic d F P0 (X - Xprime) =
        (∫ Q, (transferRate d F P0 Q : ℂ) * E Q) / Γ := by
      unfold frozenCharacteristic
      rw [← integral_div]; congr 1; funext Q; simp only [hE, ← hΓ]; push_cast; ring
    unfold frozenPositionGenerator
    have e : (fun Q => (transferRate d F P0 Q : ℂ) *
        (Complex.exp (Complex.I * (momentumDot Q (X - Xprime) / d.parameters.hbar : ℝ)) - 1) *
          r X Xprime) = fun Q => ((transferRate d F P0 Q : ℂ) * E Q - (transferRate d F P0 Q : ℂ)) *
          r X Xprime := by
      funext Q; simp only [hE]; ring
    rw [e, integral_mul_const, integral_sub hTE ?_, hphi, integral_complex_ofReal, ← hL]
    swap
    · exact hTi.ofReal
    have : (Γ : ℂ) ≠ 0 := by exact_mod_cast hΓ0
    field_simp
    ring

end QAlgorithms.Papers.Independent.Intake100.P64

end
