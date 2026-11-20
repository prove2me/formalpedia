-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P64.quantum_structureRepresentation
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T10:40:34.259193+00:00
-- url     : https://prove2.me/submissions/878e5454-4ad9-43a5-83c4-0be920f37f8c

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

theorem _root_.solution (d : CollisionData) (F : TransverseFrames)
    (beta : ℝ) (hbeta : 0 < beta)
    (hgas : ∀ p, d.gas.value p = maxwell d.parameters.m beta p)
    (r : MomentumKernel) (P Pprime : Momentum) (hdom : KernelDomain d F r P Pprime) :
    (∀ p P0 Q, collisionCoefficient d p P0 Q = structureCoefficient d beta p P0 Q) ∧
    collisionKernel d F r P Pprime = structureQuantumKernel d F beta r P Pprime := by
  have h1 : ∀ p P0 Q, collisionCoefficient d p P0 Q = structureCoefficient d beta p P0 Q := by
    intro p P0 Q
    by_cases hQ : Q = 0
    · simp [collisionCoefficient, structureCoefficient, maxwellStructure, hQ]
    have hm := d.parameters.m_pos
    have hn := d.parameters.density_pos
    have hnQ : 0 < ‖Q‖ := norm_pos_iff.mpr hQ
    have hpre : prefactor d.parameters Q =
        d.parameters.density / reducedMass d.parameters ^ 2 * (d.parameters.m / ‖Q‖) := by
      simp only [prefactor, if_neg hQ]; field_simp
    have hpt := AuxMS_pt d.parameters beta hbeta p P0 Q hQ
    have hA : 0 ≤ d.parameters.density / reducedMass d.parameters ^ 2 := by positivity
    have hB : 0 ≤ d.parameters.m / ‖Q‖ := by positivity
    have hC : 0 ≤ maxwellPlane d.parameters.m beta (perpendicular p Q) := by
      unfold maxwellPlane; positivity
    have key : Real.sqrt (prefactor d.parameters Q) *
        Real.sqrt (d.gas.value (gasArgument d.parameters p P0 Q)) =
        Real.sqrt (d.parameters.density / reducedMass d.parameters ^ 2 *
          maxwellPlane d.parameters.m beta (perpendicular p Q)) *
        Real.sqrt (maxwellStructure d.parameters beta Q (energyTransfer d.parameters Q P0)) := by
      rw [← Real.sqrt_mul (by rw [hpre]; positivity), ← Real.sqrt_mul (by positivity), hgas, hpre,
        mul_assoc, hpt, mul_assoc]
    simp only [collisionCoefficient, structureCoefficient, if_neg hQ]
    calc (Real.sqrt (prefactor d.parameters Q) : ℂ) *
          d.amplitude (transverseRelative d.parameters p P0 Q - (1 / 2 : ℝ) • Q)
            (transverseRelative d.parameters p P0 Q + (1 / 2 : ℝ) • Q) *
          (Real.sqrt (d.gas.value (gasArgument d.parameters p P0 Q)) : ℂ)
        = d.amplitude (transverseRelative d.parameters p P0 Q - (1 / 2 : ℝ) • Q)
            (transverseRelative d.parameters p P0 Q + (1 / 2 : ℝ) • Q) *
          ((Real.sqrt (prefactor d.parameters Q) *
            Real.sqrt (d.gas.value (gasArgument d.parameters p P0 Q)) : ℝ) : ℂ) := by
          push_cast; ring
      _ = _ := by rw [key]; push_cast; ring
  refine ⟨h1, ?_⟩
  unfold collisionKernel structureQuantumKernel lindbladIntegrand
  simp only [h1]

end QAlgorithms.Papers.Independent.Intake100.P64

end
