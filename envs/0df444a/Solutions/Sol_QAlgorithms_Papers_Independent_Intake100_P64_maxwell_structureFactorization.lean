-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P64.maxwell_structureFactorization
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T10:41:41.527859+00:00
-- url     : https://prove2.me/submissions/6f6b6a9a-f370-4ae3-afb0-9024d588515c

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

theorem _root_.solution (a : GasTracerParameters) (F : TransverseFrames)
    (beta : ℝ) (hbeta : 0 < beta) (Q P : Momentum) (hQ : Q ≠ 0) :
    (a.m / ‖Q‖ * ∫ k : Renew46.P04.Plane ℝ,
      maxwell a.m beta (F.map Q k +
        ((‖Q‖ ^ 2 + 2 * a.m * energyTransfer a Q P) / (2 * ‖Q‖ ^ 2)) • Q)) =
      maxwellStructure a beta Q (energyTransfer a Q P) ∧
    (∀ k : Renew46.P04.Plane ℝ, a.m / ‖Q‖ * maxwell a.m beta (gasArgument a (F.map Q k) P Q) =
      maxwellPlane a.m beta (F.map Q k) * maxwellStructure a beta Q (energyTransfer a Q P)) := by
  have hm := a.m_pos
  have hnQ : 0 < ‖Q‖ := norm_pos_iff.mpr hQ
  have hq2 : (0 : ℝ) < ‖Q‖ ^ 2 := by positivity
  have horth : ∀ k, inner ℝ (F.map Q k) Q = 0 := fun k => by
    rw [← AuxMS_dot]; exact F.orthogonal Q k
  refine ⟨?_, fun k => ?_⟩
  · set E := energyTransfer a Q P
    set t : ℝ := (‖Q‖ ^ 2 + 2 * a.m * E) / (2 * ‖Q‖ ^ 2) with ht
    set b : ℝ := beta / (2 * a.m) with hb
    have hb0 : 0 < b := by positivity
    have hW : 0 < beta / (2 * Real.pi * a.m) := by positivity
    have hnorm : ∀ k, ‖F.map Q k + t • Q‖ ^ 2 = ‖k‖ ^ 2 + t ^ 2 * ‖Q‖ ^ 2 := by
      intro k
      rw [norm_add_sq_real, inner_smul_right, horth, LinearIsometry.norm_map, norm_smul, mul_pow,
        Real.norm_eq_abs, sq_abs]
      ring
    have hfun : (fun k : Renew46.P04.Plane ℝ => maxwell a.m beta (F.map Q k + t • Q)) =
        fun k => (Real.rpow (beta / (2 * Real.pi * a.m)) (3 / 2 : ℝ) *
          Real.exp (-beta * (t ^ 2 * ‖Q‖ ^ 2) / (2 * a.m))) * Real.exp (-b * ‖k‖ ^ 2) := by
      funext k
      simp only [maxwell, hnorm, hb]
      rw [mul_assoc _ (Real.exp _) (Real.exp _), ← Real.exp_add]
      congr 2
      field_simp
      ring
    rw [hfun, integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm hb0, finrank_euclideanSpace,
      Fintype.card_fin]
    have hrp : Real.rpow (beta / (2 * Real.pi * a.m)) (3 / 2 : ℝ) =
        beta / (2 * Real.pi * a.m) * Real.sqrt (beta / (2 * Real.pi * a.m)) := by
      rw [Real.rpow_eq_pow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hW,
        Real.rpow_one, Real.sqrt_eq_rpow]
    have hsq : Real.sqrt (beta * a.m / (2 * Real.pi)) =
        a.m * Real.sqrt (beta / (2 * Real.pi * a.m)) := by
      rw [show beta * a.m / (2 * Real.pi) = a.m ^ 2 * (beta / (2 * Real.pi * a.m)) by
        field_simp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hm.le]
    have hex : -beta * (t ^ 2 * ‖Q‖ ^ 2) / (2 * a.m) =
        -beta * (‖Q‖ ^ 2 + 2 * a.m * E) ^ 2 / (8 * a.m * ‖Q‖ ^ 2) := by
      rw [ht]; field_simp; ring
    simp only [maxwellStructure, if_neg hQ, hrp, hsq, hex]
    rw [show ((2 : ℕ) : ℝ) / 2 = 1 by norm_num, Real.rpow_one, hb]
    have hpi := Real.pi_pos
    field_simp
  · have hperp : perpendicular (F.map Q k) Q = F.map Q k := by
      simp [perpendicular, parallel, F.orthogonal Q k]
    rw [AuxMS_pt a beta hbeta _ P Q hQ, hperp]

end QAlgorithms.Papers.Independent.Intake100.P64

end
