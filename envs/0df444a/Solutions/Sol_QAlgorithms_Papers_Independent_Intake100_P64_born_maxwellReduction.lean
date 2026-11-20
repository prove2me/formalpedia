-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P64.born_maxwellReduction
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T10:46:44.294838+00:00
-- url     : https://prove2.me/submissions/c6dea2ce-6bf5-4aec-a852-e5f9123edfa1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

theorem AuxMS_dot (x y : Momentum) : momentumDot x y = inner ℝ x y := by
  simp [momentumDot, PiLp.inner_apply, mul_comm]

theorem AuxMS_pt (a : GasTracerParameters) (beta : ℝ) (hbeta : 0 < beta) (p P Q : Momentum)
    (hQ : Q ≠ 0) :
    a.m / ‖Q‖ * maxwell a.m beta (gasArgument a p P Q) =
      maxwellPlane a.m beta (perpendicular p Q) * maxwellStructure a beta Q (energyTransfer a Q P) := by
  have hm := a.m_pos
  have hM := a.M_pos
  have hnQ : 0 < ‖Q‖ := norm_pos_iff.mpr hQ
  have hq2 : (0 : ℝ) < ‖Q‖ ^ 2 := by positivity
  set u := perpendicular p Q with hu
  set s := momentumDot P Q with hs
  set c : ℝ := a.m / (2 * reducedMass a) + a.m / a.M * (s / ‖Q‖ ^ 2) with hc
  have hg : gasArgument a p P Q = u + c • Q := by
    simp only [gasArgument, hu, parallel, hc, add_smul, smul_smul, hs]
    abel
  have hQQ : inner ℝ Q Q = ‖Q‖ ^ 2 := real_inner_self_eq_norm_sq Q
  have huQ : inner ℝ u Q = 0 := by
    simp only [hu, perpendicular, parallel, inner_sub_left, inner_smul_left, hQQ, AuxMS_dot]
    simp only [RCLike.conj_to_real]
    field_simp
    ring
  have hn : ‖gasArgument a p P Q‖ ^ 2 = ‖u‖ ^ 2 + c ^ 2 * ‖Q‖ ^ 2 := by
    rw [hg, norm_add_sq_real, inner_smul_right, huQ, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs]
    ring
  have hE : energyTransfer a Q P = ‖Q‖ ^ 2 / (2 * a.M) + s / a.M := by
    simp only [energyTransfer, hs, AuxMS_dot, real_inner_comm]
  have hcq : c * ‖Q‖ ^ 2 = (‖Q‖ ^ 2 + 2 * a.m * energyTransfer a Q P) / 2 := by
    rw [hE, hc, reducedMass]
    field_simp
    ring
  have hw : 0 < beta / (2 * Real.pi * a.m) := by positivity
  have hrp : Real.rpow (beta / (2 * Real.pi * a.m)) (3 / 2 : ℝ) =
      beta / (2 * Real.pi * a.m) * Real.sqrt (beta / (2 * Real.pi * a.m)) := by
    rw [Real.rpow_eq_pow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hw,
      Real.rpow_one, Real.sqrt_eq_rpow]
  have hsq : Real.sqrt (beta * a.m / (2 * Real.pi)) = a.m * Real.sqrt (beta / (2 * Real.pi * a.m)) := by
    rw [show beta * a.m / (2 * Real.pi) = a.m ^ 2 * (beta / (2 * Real.pi * a.m)) by
      field_simp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hm.le]
  simp only [maxwell, maxwellPlane, maxwellStructure, if_neg hQ, hrp, hsq, hn]
  have hexp : Real.exp (-beta * (‖u‖ ^ 2 + c ^ 2 * ‖Q‖ ^ 2) / (2 * a.m)) =
      Real.exp (-beta * ‖u‖ ^ 2 / (2 * a.m)) *
        Real.exp (-beta * (‖Q‖ ^ 2 + 2 * a.m * energyTransfer a Q P) ^ 2 /
          (8 * a.m * ‖Q‖ ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    rw [show (‖Q‖ ^ 2 + 2 * a.m * energyTransfer a Q P) = 2 * (c * ‖Q‖ ^ 2) by linarith [hcq]]
    field_simp
    ring
  rw [hexp]
  field_simp
theorem AuxCS_plane (m beta : ℝ) (hm : 0 < m) (hbeta : 0 < beta) (F : TransverseFrames)
    (Q : Momentum) : ∫ k : Renew46.P04.Plane ℝ, maxwellPlane m beta (F.map Q k) = 1 := by
  have hb : 0 < beta / (2 * m) := by positivity
  have e : (fun k : Renew46.P04.Plane ℝ => maxwellPlane m beta (F.map Q k)) =
      fun k => beta / (2 * Real.pi * m) * Real.exp (-(beta / (2 * m)) * ‖k‖ ^ 2) := by
    funext k; simp only [maxwellPlane, LinearIsometry.norm_map]; congr 2; ring
  rw [e, integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm hb,
    finrank_euclideanSpace, Fintype.card_fin, show ((2 : ℕ) : ℝ) / 2 = 1 by norm_num,
    Real.rpow_one]
  have := Real.pi_pos
  field_simp


theorem AuxB_mat (a : GasTracerParameters) (V : Momentum → ℝ) (pf pi : Momentum) :
    bornMatrixAmplitude a V pf pi = bornAmplitude a V (pf - pi) := by
  unfold bornMatrixAmplitude bornAmplitude
  congr 2; funext x
  congr 4
  simp only [momentumDot, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem AuxB_neg (a : GasTracerParameters) (V : Momentum → ℝ) (Q : Momentum) :
    Complex.normSq (bornAmplitude a V (-Q)) = Complex.normSq (bornAmplitude a V Q) := by
  have h : bornAmplitude a V (-Q) = (starRingEnd ℂ) (bornAmplitude a V Q) := by
    unfold bornAmplitude
    rw [map_mul, Complex.conj_ofReal, ← integral_conj]
    congr 2; funext x
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 1
    simp only [momentumDot, PiLp.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_div,
      Complex.ofReal_neg, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [h, Complex.normSq_conj]

theorem AuxB_c (d : CollisionData) (F : TransverseFrames) (V : Momentum → ℝ) (beta : ℝ)
    (hbeta : 0 < beta)
    (hgas : ∀ p, d.gas.value p = maxwell d.parameters.m beta p)
    (hf : ∀ pf pi, d.amplitude pf pi = bornMatrixAmplitude d.parameters V pf pi)
    (Q : Momentum) (hQ : Q ≠ 0) (P0 : Momentum) (k : Renew46.P04.Plane ℝ) :
    collisionCoefficient d (F.map Q k) P0 Q = bornAmplitude d.parameters V (-Q) *
      ((Real.sqrt (d.parameters.density / reducedMass d.parameters ^ 2 *
        maxwellPlane d.parameters.m beta (F.map Q k)) *
       Real.sqrt (maxwellStructure d.parameters beta Q (energyTransfer d.parameters Q P0)) : ℝ) : ℂ) := by
  have hm := d.parameters.m_pos
  have hn := d.parameters.density_pos
  have hnQ : 0 < ‖Q‖ := norm_pos_iff.mpr hQ
  have hperp : perpendicular (F.map Q k) Q = F.map Q k := by
    simp [perpendicular, parallel, F.orthogonal Q k]
  have hpt := AuxMS_pt d.parameters beta hbeta (F.map Q k) P0 Q hQ
  rw [hperp] at hpt
  have hpre : prefactor d.parameters Q =
      d.parameters.density / reducedMass d.parameters ^ 2 * (d.parameters.m / ‖Q‖) := by
    simp only [prefactor, if_neg hQ]; field_simp
  have hC : 0 ≤ maxwellPlane d.parameters.m beta (F.map Q k) := by
    unfold maxwellPlane; positivity
  have key : Real.sqrt (prefactor d.parameters Q) *
      Real.sqrt (d.gas.value (gasArgument d.parameters (F.map Q k) P0 Q)) =
      Real.sqrt (d.parameters.density / reducedMass d.parameters ^ 2 *
        maxwellPlane d.parameters.m beta (F.map Q k)) *
      Real.sqrt (maxwellStructure d.parameters beta Q (energyTransfer d.parameters Q P0)) := by
    rw [← Real.sqrt_mul (by rw [hpre]; positivity), ← Real.sqrt_mul (by positivity), hgas, hpre,
      mul_assoc, hpt, mul_assoc]
  have hx : ∀ x : Momentum, (x - (1 / 2 : ℝ) • Q) - (x + (1 / 2 : ℝ) • Q) = -Q := fun x => by
    module
  simp only [collisionCoefficient, if_neg hQ, hf, AuxB_mat, hx]
  rw [← key]; push_cast; ring

theorem AuxB_m (a : GasTracerParameters) (V : Momentum → ℝ) (beta : ℝ) (hbeta : 0 < beta)
    (Q : Momentum) (hQ : Q ≠ 0) (P0 : Momentum) :
    bornMultiplier a beta V P0 Q =
      Real.sqrt (a.density / reducedMass a ^ 2 * Complex.normSq (bornAmplitude a V Q)) *
      Real.sqrt (maxwellStructure a beta Q (energyTransfer a Q P0)) := by
  have hm := a.m_pos
  have hM := a.M_pos
  have hn := a.density_pos
  have hnQ : 0 < ‖Q‖ := norm_pos_iff.mpr hQ
  have hq2 : (0 : ℝ) < ‖Q‖ ^ 2 := by positivity
  unfold bornMultiplier maxwellStructure
  rw [if_neg hQ, if_neg hQ]
  have hAN : 0 ≤ a.density / reducedMass a ^ 2 * Complex.normSq (bornAmplitude a V Q) :=
    mul_nonneg (div_nonneg hn.le (sq_nonneg _)) (Complex.normSq_nonneg _)
  rw [← Real.sqrt_mul hAN, ← mul_assoc, Real.sqrt_mul (mul_nonneg hAN (by positivity)),
    ← Real.exp_half]
  have hE : energyTransfer a Q P0 = ‖Q‖ ^ 2 / (2 * a.M) + momentumDot P0 Q / a.M := by
    simp only [energyTransfer, AuxMS_dot, real_inner_comm]
  congr 2
  · field_simp
  · rw [hE]; field_simp; ring

theorem _root_.solution (d : CollisionData) (F : TransverseFrames)
    (V : Momentum → ℝ) (beta : ℝ) (hbeta : 0 < beta) (hV : Integrable V)
    (hgas : ∀ p, d.gas.value p = maxwell d.parameters.m beta p)
    (hf : ∀ pf pi, d.amplitude pf pi = bornMatrixAmplitude d.parameters V pf pi)
    (r : MomentumKernel) (P Pprime : Momentum) (hdom : KernelDomain d F r P Pprime) :
    collisionKernel d F r P Pprime = bornKernel d.parameters beta V r P Pprime ∧
    (∀ P0, energyShift d P0 =
      -2 * Real.pi * d.parameters.hbar ^ 2 * d.parameters.density /
        reducedMass d.parameters * (bornAmplitude d.parameters V 0).re) := by
  refine ⟨?_, fun P0 => ?_⟩
  · unfold collisionKernel bornKernel
    congr 1; funext Q
    by_cases hQ : Q = 0
    · simp [lindbladIntegrand, collisionCoefficient, bornMultiplier, hQ]
    have hm := d.parameters.m_pos
    have hn := d.parameters.density_pos
    set A := d.parameters.density / reducedMass d.parameters ^ 2 with hA
    have hA0 : 0 ≤ A := by positivity
    set N := Complex.normSq (bornAmplitude d.parameters V Q) with hN
    have hN0 : 0 ≤ N := Complex.normSq_nonneg _
    have hS : ∀ P0, 0 ≤ maxwellStructure d.parameters beta Q (energyTransfer d.parameters Q P0) := by
      intro P0; unfold maxwellStructure; rw [if_neg hQ]; positivity
    set s := fun P0 => Real.sqrt (maxwellStructure d.parameters beta Q (energyTransfer d.parameters Q P0))
      with hs
    have hpw : ∀ k, (lindbladIntegrand d F r P Pprime Q k) =
        ((maxwellPlane d.parameters.m beta (F.map Q k) : ℝ) : ℂ) *
        ((bornMultiplier d.parameters beta V (P - Q) Q : ℂ) * r (P - Q) (Pprime - Q) *
          (bornMultiplier d.parameters beta V (Pprime - Q) Q : ℂ) -
        (((bornMultiplier d.parameters beta V P Q ^ 2 +
          bornMultiplier d.parameters beta V Pprime Q ^ 2) / 2 : ℝ) : ℂ) * r P Pprime) := by
      intro k
      have hC : 0 ≤ maxwellPlane d.parameters.m beta (F.map Q k) := by
        unfold maxwellPlane; positivity
      unfold lindbladIntegrand
      simp only [AuxB_c d F V beta hbeta hgas hf Q hQ, AuxB_m d.parameters V beta hbeta Q hQ,
        Complex.normSq_mul, Complex.normSq_ofReal, AuxB_neg, star_mul', Complex.star_def,
        Complex.conj_ofReal]
      have e1 : bornAmplitude d.parameters V (-Q) * (starRingEnd ℂ) (bornAmplitude d.parameters V (-Q))
          = (N : ℂ) := by rw [Complex.mul_conj, AuxB_neg]
      have hsq1 : Real.sqrt (A * maxwellPlane d.parameters.m beta (F.map Q k)) ^ 2
          = A * maxwellPlane d.parameters.m beta (F.map Q k) := Real.sq_sqrt (by positivity)
      have hsq2 : Real.sqrt (A * N) ^ 2 = A * N := Real.sq_sqrt (by positivity)
      have hsP : ∀ P0, Real.sqrt (maxwellStructure d.parameters beta Q (energyTransfer d.parameters Q P0)) ^ 2
          = maxwellStructure d.parameters beta Q (energyTransfer d.parameters Q P0) :=
        fun P0 => Real.sq_sqrt (hS P0)
      have hm1 : Real.sqrt (A * maxwellPlane d.parameters.m beta (F.map Q k)) *
          Real.sqrt (A * maxwellPlane d.parameters.m beta (F.map Q k)) =
          A * maxwellPlane d.parameters.m beta (F.map Q k) := Real.mul_self_sqrt (by positivity)
      have hm2 : Real.sqrt (A * N) * Real.sqrt (A * N) = A * N := Real.mul_self_sqrt (by positivity)
      have hsP' : ∀ P0, Real.sqrt (maxwellStructure d.parameters beta Q (energyTransfer d.parameters Q P0)) *
          Real.sqrt (maxwellStructure d.parameters beta Q (energyTransfer d.parameters Q P0))
          = maxwellStructure d.parameters beta Q (energyTransfer d.parameters Q P0) :=
        fun P0 => Real.mul_self_sqrt (hS P0)
      calc _ = (bornAmplitude d.parameters V (-Q) * (starRingEnd ℂ) (bornAmplitude d.parameters V (-Q))) *
            ((Real.sqrt (A * maxwellPlane d.parameters.m beta (F.map Q k)) *
              Real.sqrt (A * maxwellPlane d.parameters.m beta (F.map Q k)) : ℝ) : ℂ) *
            ((s (P - Q) * s (Pprime - Q) : ℝ) : ℂ) * r (P - Q) (Pprime - Q) -
            (((Complex.normSq (bornAmplitude d.parameters V Q) *
              (Real.sqrt (A * maxwellPlane d.parameters.m beta (F.map Q k)) *
               Real.sqrt (A * maxwellPlane d.parameters.m beta (F.map Q k))) *
              ((s P * s P + s Pprime * s Pprime) / 2) : ℝ) : ℂ)) * r P Pprime := by
            simp only [hs]; push_cast; ring
        _ = _ := by
            rw [e1, hm1]
            have hu : ((Real.sqrt (A * N) : ℝ) : ℂ) * ((Real.sqrt (A * N) : ℝ) : ℂ)
                = ((A * N : ℝ) : ℂ) := by rw [← Complex.ofReal_mul, hm2]
            simp only [hs]
            push_cast at hu ⊢
            linear_combination (-((maxwellPlane d.parameters.m beta (F.map Q k) : ℝ) : ℂ) *
              (((s (P - Q) : ℝ) : ℂ) * ((s (Pprime - Q) : ℝ) : ℂ) * r (P - Q) (Pprime - Q) -
                ((((s P : ℝ) : ℂ) * ((s P : ℝ) : ℂ) + ((s Pprime : ℝ) : ℂ) * ((s Pprime : ℝ) : ℂ)) / 2) *
                  r P Pprime)) * hu
    simp_rw [hpw]
    rw [integral_mul_const, integral_complex_ofReal, AuxCS_plane _ _ d.parameters.m_pos hbeta]
    simp
  · unfold energyShift forwardAverage
    congr 3
    simp only [hf, AuxB_mat, sub_self]
    rw [integral_mul_const, integral_complex_ofReal, d.gas.normalized]
    simp

end QAlgorithms.Papers.Independent.Intake100.P64

end
