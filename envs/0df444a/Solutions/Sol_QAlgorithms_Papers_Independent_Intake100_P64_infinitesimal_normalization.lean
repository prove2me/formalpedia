-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P64.infinitesimal_normalization
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T10:36:48.649961+00:00
-- url     : https://prove2.me/submissions/fafc72bc-0511-4866-8ed0-5e9d0f2da6ca

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

theorem AuxCDR_gain (d : CollisionData) (F : TransverseFrames) (P Q : Momentum) :
    quantumGain d F P P Q = (transferRate d F (P - Q) Q : ℂ) := by
  unfold quantumGain transferRate
  rw [← integral_complex_ofReal]
  congr 1; funext k
  rw [Complex.star_def, Complex.mul_conj, AuxCDR_normSq]
  rfl

theorem AuxIN_cdr (d : CollisionData) (F : TransverseFrames)
    (r : MomentumKernel) (nu : Momentum → ℝ) (P : Momentum)
    (hdiag : ∀ p, r p p = (nu p : ℂ)) (hdom : KernelDomain d F r P P) :
    (∀ Q, Integrable (rateIntegrand d F (P - Q) Q) →
      quantumGain d F P P Q = (transferRate d F (P - Q) Q : ℂ)) ∧
    collisionKernel d F r P P = (classicalGenerator d F nu P : ℂ) := by
  refine ⟨fun Q _ => AuxCDR_gain d F P Q, ?_⟩
  obtain ⟨h1, h2, _, h4, h5, _⟩ := hdom
  have hin : ∀ᵐ Q : Momentum, ∫ k, lindbladIntegrand d F r P P Q k =
      quantumGain d F P P Q * r (P - Q) (P - Q) - (outgoingIntensity d F P Q : ℂ) * r P P := by
    filter_upwards [h1, h2] with Q a1 a2
    have e : (fun k => lindbladIntegrand d F r P P Q k) = fun k =>
        collisionCoefficient d (F.map Q k) (P - Q) Q *
          star (collisionCoefficient d (F.map Q k) (P - Q) Q) * r (P - Q) (P - Q) -
        ((Complex.normSq (collisionCoefficient d (F.map Q k) P Q) : ℝ) : ℂ) * r P P := by
      funext k; unfold lindbladIntegrand; simp only [add_self_div_two]; ring
    rw [e, integral_sub (a1.mul_const _) ?_, integral_mul_const,
      integral_mul_const, integral_complex_ofReal]
    · rfl
    · exact a2.ofReal.mul_const _
  unfold collisionKernel classicalGenerator collisionLossRate
  rw [integral_congr_ae hin, integral_sub h4 ?_, integral_mul_const,
    integral_complex_ofReal]
  swap
  · exact h5.ofReal.mul_const _
  have : (fun Q => quantumGain d F P P Q * r (P - Q) (P - Q)) =
      fun Q => ((transferRate d F (P - Q) Q * nu (P - Q) : ℝ) : ℂ) := by
    funext Q; rw [AuxCDR_gain, hdiag]; push_cast; ring
  rw [this, integral_complex_ofReal, hdiag]
  push_cast; ring


theorem _root_.solution (d : CollisionData) (F : TransverseFrames)
    (nu : MomentumLaw)
    (hplane : ∀ P, ∀ᵐ Q : Momentum, Integrable (rateIntegrand d F P Q))
    (hloss : ∀ P, Integrable (outgoingIntensity d F P))
    (hdouble : Integrable (fun z : Momentum × Momentum =>
      transferRate d F z.1 z.2 * nu.value z.1)) :
    (∀ P, collisionLossRate d F P = ∫ Q, transferRate d F P Q) ∧
    (∫ P, classicalGenerator d F nu.value P) = 0 ∧
    (∀ r : MomentumKernel, (∀ P, r P P = (nu.value P : ℂ)) →
      (∀ P, KernelDomain d F r P P) → (∫ P, collisionKernel d F r P P) = 0) := by
  have hL : ∀ P, collisionLossRate d F P = ∫ Q, transferRate d F P Q := by
    intro P
    unfold collisionLossRate outgoingIntensity transferRate
    congr 1; funext Q; congr 1; funext k
    rw [AuxCDR_normSq]; rfl
  have hgen : (∫ P, classicalGenerator d F nu.value P) = 0 := by
    set f : Momentum → Momentum → ℝ := fun P Q => transferRate d F P Q * nu.value P with hf
    have hd : Integrable (Function.uncurry f) (volume.prod volume) := hdouble
    have hg : Integrable (fun z : Momentum × Momentum => f (z.1 - z.2) z.2)
        (volume.prod volume) :=
      ((measurePreserving_sub_prod volume volume).integrable_comp
        hd.aestronglyMeasurable).mpr hd
    have hshift : (∫ P, ∫ Q, f (P - Q) Q) = ∫ P, ∫ Q, f P Q := by
      have hg' : Integrable (Function.uncurry fun P Q => f (P - Q) Q) (volume.prod volume) := hg
      rw [integral_integral_swap hg', integral_integral_swap hd]
      congr 1; funext Q; exact integral_sub_right_eq_self (fun P => f P Q) Q
    unfold classicalGenerator
    simp_rw [hL]
    have e2 : ∀ P, (∫ Q, transferRate d F P Q) * nu.value P = ∫ Q, f P Q := by
      intro P; rw [← integral_mul_const]
    simp_rw [e2]
    rw [integral_sub ?_ ?_]
    · rw [sub_eq_zero]; exact hshift
    · exact hg.integral_prod_left
    · exact hd.integral_prod_left
  refine ⟨hL, hgen, fun r hr hdom => ?_⟩
  have : (fun P => collisionKernel d F r P P) = fun P => ((classicalGenerator d F nu.value P : ℝ) : ℂ) :=
    funext fun P => (AuxIN_cdr d F r nu.value P hr (hdom P)).2
  rw [this, integral_complex_ofReal, hgen]; simp

end QAlgorithms.Papers.Independent.Intake100.P64

end
