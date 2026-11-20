-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P64.classical_structureRepresentation
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T10:43:00.168994+00:00
-- url     : https://prove2.me/submissions/64c4fb3e-a694-4b67-a438-9f51a13047a2

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


theorem AuxCS_T (d : CollisionData) (F : TransverseFrames) (beta : ℝ) (hbeta : 0 < beta)
    (hgas : ∀ p, d.gas.value p = maxwell d.parameters.m beta p) (P Q : Momentum) :
    transferRate d F P Q = d.parameters.density / reducedMass d.parameters ^ 2 *
      maxwellStructure d.parameters beta Q (energyTransfer d.parameters Q P) *
        averagedCrossSection d F beta P Q := by
  by_cases hQ : Q = 0
  · simp [transferRate, rateIntegrand, prefactor, maxwellStructure, hQ]
  have hnQ : 0 < ‖Q‖ := norm_pos_iff.mpr hQ
  unfold transferRate averagedCrossSection
  rw [← integral_const_mul]
  congr 1; funext k
  have hperp : perpendicular (F.map Q k) Q = F.map Q k := by
    simp [perpendicular, parallel, F.orthogonal Q k]
  have hpt := AuxMS_pt d.parameters beta hbeta (F.map Q k) P Q hQ
  rw [hperp] at hpt
  have hpre : prefactor d.parameters Q =
      d.parameters.density / reducedMass d.parameters ^ 2 * (d.parameters.m / ‖Q‖) := by
    simp only [prefactor, if_neg hQ]; field_simp
  simp only [rateIntegrand, hgas, hpre]
  rw [mul_assoc (d.parameters.density / reducedMass d.parameters ^ 2) (d.parameters.m / ‖Q‖), hpt]
  ring

theorem AuxCS_avg_shift (d : CollisionData) (F : TransverseFrames) (beta : ℝ) (P Q : Momentum) :
    averagedCrossSection d F beta (P - Q) Q = averagedCrossSection d F beta P Q := by
  have h : perpendicular (P - Q) Q = perpendicular P Q := by
    by_cases hQ : Q = 0
    · subst hQ; simp
    have hq : ‖Q‖ ^ 2 ≠ 0 := by positivity
    simp only [perpendicular, parallel, momentumDot, PiLp.sub_apply, sub_mul,
      Finset.sum_sub_distrib]
    rw [show (∑ i, Q i * Q i) = ‖Q‖ ^ 2 by
      rw [EuclideanSpace.norm_sq_eq]; simp [sq]]
    rw [sub_div, div_self hq, sub_smul, one_smul]
    abel
  simp only [averagedCrossSection, transverseRelative, h]

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

theorem _root_.solution (d : CollisionData) (F : TransverseFrames)
    (beta : ℝ) (hbeta : 0 < beta)
    (hgas : ∀ p, d.gas.value p = maxwell d.parameters.m beta p)
    (nu : Momentum → ℝ) (P : Momentum)
    (hplane : ∀ᵐ Q : Momentum, Integrable (rateIntegrand d F P Q) ∧
      Integrable (rateIntegrand d F (P - Q) Q))
    (hgain : Integrable (fun Q => transferRate d F (P - Q) Q * nu (P - Q)))
    (hloss : Integrable (outgoingIntensity d F P)) :
    classicalGenerator d F nu P = structureGenerator d F beta
      (fun Q p => maxwellStructure d.parameters beta Q (energyTransfer d.parameters Q p)) nu P ∧
    (∀ sigma : Momentum → ℝ,
      (∀ pf pi, crossSection d pf pi = sigma (pf - pi)) →
      ∀ Q, averagedCrossSection d F beta P Q = sigma (-Q)) := by
  have hT : ∀ Q, transferRate d F P Q = outgoingIntensity d F P Q := by
    intro Q; unfold transferRate outgoingIntensity
    congr 1; funext k; rw [AuxCDR_normSq]; rfl
  have hTi : Integrable (fun Q => transferRate d F P Q) := by simpa only [hT] using hloss
  refine ⟨?_, fun sigma hs Q => ?_⟩
  · unfold classicalGenerator structureGenerator collisionLossRate
    simp only [← hT]
    rw [← integral_mul_const, ← integral_sub hgain (hTi.mul_const _), ← integral_const_mul]
    congr 1; funext Q
    rw [AuxCS_T d F beta hbeta hgas, AuxCS_T d F beta hbeta hgas, AuxCS_avg_shift]
    ring
  · unfold averagedCrossSection
    simp only [hs]
    have hx : ∀ x : Momentum, (x - (1 / 2 : ℝ) • Q) - (x + (1 / 2 : ℝ) • Q) = -Q := fun x => by
      module
    simp only [hx]
    rw [integral_mul_const, AuxCS_plane _ _ d.parameters.m_pos hbeta, one_mul]

end QAlgorithms.Papers.Independent.Intake100.P64

end
