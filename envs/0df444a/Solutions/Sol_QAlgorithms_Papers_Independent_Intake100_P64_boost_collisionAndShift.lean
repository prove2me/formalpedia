-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P64.boost_collisionAndShift
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-11-19T02:29:05.251719+00:00
-- url     : https://prove2.me/submissions/9ef6096f-ed39-4498-845a-d8a8c5b4076d

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter
open QAlgorithms.Papers.Independent.Intake100.P64
open scoped BigOperators ENNReal NNReal Topology

local notation "Plane" => QAlgorithms.Papers.Independent.Renew46.P04.Plane ℝ

private theorem dot_eq_inner (x y : Momentum) : momentumDot x y = inner ℝ x y := by
  simp only [momentumDot, PiLp.inner_apply, Real.inner_apply]

private theorem parallel_add' (x y Q : Momentum) :
    parallel (x + y) Q = parallel x Q + parallel y Q := by
  simp only [parallel, dot_eq_inner, inner_add_left, add_div, add_smul]

private theorem parallel_sub' (x y Q : Momentum) :
    parallel (x - y) Q = parallel x Q - parallel y Q := by
  simp only [parallel, dot_eq_inner, inner_sub_left, sub_div, sub_smul]

private theorem parallel_smul' (c : ℝ) (x Q : Momentum) :
    parallel (c • x) Q = c • parallel x Q := by
  simp only [parallel, dot_eq_inner, real_inner_smul_left, mul_div_assoc, mul_smul]

private theorem parallel_idempotent (x Q : Momentum) :
    parallel (parallel x Q) Q = parallel x Q := by
  by_cases hQ : Q = 0
  · simp [parallel, hQ]
  · have hQQ : parallel Q Q = Q := by
      simp only [parallel, dot_eq_inner, real_inner_self_eq_norm_sq,
        div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr hQ)), one_smul]
    change parallel ((momentumDot x Q / ‖Q‖ ^ 2) • Q) Q = _
    rw [parallel_smul', hQQ]
    rfl

private theorem perp_add (x y Q : Momentum) :
    perpendicular (x + y) Q = perpendicular x Q + perpendicular y Q := by
  simp only [perpendicular, parallel_add']
  abel

private theorem perp_sub (x y Q : Momentum) :
    perpendicular (x - y) Q = perpendicular x Q - perpendicular y Q := by
  simp only [perpendicular, parallel_sub']
  abel

private theorem perp_smul (c : ℝ) (x Q : Momentum) :
    perpendicular (c • x) Q = c • perpendicular x Q := by
  simp only [perpendicular, parallel_smul', smul_sub]

private theorem perp_idempotent (x Q : Momentum) :
    perpendicular (perpendicular x Q) Q = perpendicular x Q := by
  simp only [perpendicular, parallel_sub', parallel_idempotent, sub_self, sub_zero]

private theorem perp_orthogonal (x Q : Momentum) :
    momentumDot (perpendicular x Q) Q = 0 := by
  by_cases hQ : Q = 0
  · simp [dot_eq_inner, hQ]
  · simp only [perpendicular, parallel, dot_eq_inner, inner_sub_left,
      real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [div_mul_cancel₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hQ)), sub_self]

private theorem relative_boost (a : GasTracerParameters) (p P v : Momentum) :
    relativeMomentum a (p - a.m • v) (P - a.M • v) = relativeMomentum a p P := by
  unfold relativeMomentum
  match_scalars <;> first | ring1 | (field_simp [a.m_pos.ne', a.M_pos.ne'] <;> ring)

private theorem coefficient_boost (d : CollisionData) (v P p Q : Momentum) :
    collisionCoefficient d p (P - d.parameters.M • v) Q =
      boostedCoefficient d v (p + d.parameters.m • perpendicular v Q) P Q := by
  by_cases hQ : Q = 0
  · simp [collisionCoefficient, boostedCoefficient, hQ]
  let a := d.parameters
  have hrel : transverseRelative a p (P - a.M • v) Q =
      transverseRelative a (p + a.m • perpendicular v Q) P Q := by
    simp only [transverseRelative, relativeMomentum, perp_sub, perp_add, perp_smul,
      perp_idempotent]
    match_scalars <;> first | ring1 | (field_simp [a.m_pos.ne', a.M_pos.ne'] <;> ring)
  have hgas : gasArgument a p (P - a.M • v) Q =
      gasArgument a (p + a.m • perpendicular v Q) P Q - a.m • v := by
    simp only [gasArgument, perp_add, perp_smul, perp_idempotent, parallel_sub', parallel_smul']
    simp only [perpendicular]
    match_scalars <;> first | ring1 | (field_simp [a.M_pos.ne'] <;> ring)
  simp only [collisionCoefficient, boostedCoefficient, if_neg hQ]
  rw [hrel, hgas]

private theorem shift_boost (d : CollisionData) (v P : Momentum) :
    energyShift d (P - d.parameters.M • v) = boostedEnergyShift d v P := by
  let a := d.parameters
  have hrel (p : Momentum) : relativeMomentum a (p - a.m • v) (P - a.M • v) =
      relativeMomentum a p P := relative_boost a p P v
  have hint :
      (∫ p : Momentum, (d.gas.value p : ℂ) *
        d.amplitude (relativeMomentum a p (P - a.M • v))
          (relativeMomentum a p (P - a.M • v))) =
      ∫ p : Momentum, (d.gas.value (p - a.m • v) : ℂ) *
        d.amplitude (relativeMomentum a p P) (relativeMomentum a p P) := by
    rw [← integral_sub_right_eq_self (fun p : Momentum => (d.gas.value p : ℂ) *
      d.amplitude (relativeMomentum a p (P - a.M • v))
        (relativeMomentum a p (P - a.M • v))) (a.m • v)]
    apply integral_congr_ae
    filter_upwards with p
    rw [hrel]
  unfold energyShift boostedEnergyShift forwardAverage
  rw [hint]

theorem solution (d : CollisionData) (F : TransverseFrames)
    (v P : Momentum)
    (hforward : Integrable (fun p => (d.gas.value p : ℂ) *
      d.amplitude (relativeMomentum d.parameters p (P - d.parameters.M • v))
        (relativeMomentum d.parameters p (P - d.parameters.M • v)))) :
    (∀ p Q, collisionCoefficient d p (P - d.parameters.M • v) Q =
      boostedCoefficient d v (p + d.parameters.m • perpendicular v Q) P Q) ∧
    energyShift d (P - d.parameters.M • v) = boostedEnergyShift d v P ∧
    (∀ (r : MomentumKernel) (Pprime : Momentum),
      KernelDomain d F
        (fun A B => r (A + d.parameters.M • v) (B + d.parameters.M • v))
        (P - d.parameters.M • v) (Pprime - d.parameters.M • v) →
      collisionKernel d F
        (fun A B => r (A + d.parameters.M • v) (B + d.parameters.M • v))
        (P - d.parameters.M • v) (Pprime - d.parameters.M • v) =
          boostedCollisionKernel d F v r P Pprime) := by
  refine ⟨fun p Q => coefficient_boost d v P p Q, shift_boost d v P, ?_⟩
  intro r Pprime _
  let a := d.parameters
  unfold collisionKernel boostedCollisionKernel
  apply integral_congr_ae
  filter_upwards with Q
  by_cases hQ : Q = 0
  · subst Q
    simp [lindbladIntegrand, collisionCoefficient, boostedCoefficient]
  have horth : momentumDot (a.m • perpendicular v Q) Q = 0 := by
    rw [dot_eq_inner, real_inner_smul_left, ← dot_eq_inner, perp_orthogonal, mul_zero]
  obtain ⟨k0, hk0⟩ := F.onto Q hQ (a.m • perpendicular v Q) horth
  have hc (A : Momentum) (k : Plane) :
      collisionCoefficient d (F.map Q k) (A - a.M • v) Q =
        boostedCoefficient d v (F.map Q (k + k0)) A Q := by
    rw [coefficient_boost d v A, map_add, hk0]
  let integrand (k : Plane) :=
    boostedCoefficient d v (F.map Q k) (P - Q) Q *
      r (P - Q) (Pprime - Q) *
      star (boostedCoefficient d v (F.map Q k) (Pprime - Q) Q) -
    (((Complex.normSq (boostedCoefficient d v (F.map Q k) P Q) +
      Complex.normSq (boostedCoefficient d v (F.map Q k) Pprime Q)) / 2 : ℝ) : ℂ) *
      r P Pprime
  calc
    _ = ∫ k : Plane, integrand (k + k0) := by
      apply integral_congr_ae
      filter_upwards with k
      unfold lindbladIntegrand
      have hPQ : P - a.M • v - Q = (P - Q) - a.M • v := by abel
      have hPprimeQ : Pprime - a.M • v - Q = (Pprime - Q) - a.M • v := by abel
      rw [hPQ, hPprimeQ, hc (P - Q), hc (Pprime - Q), hc P, hc Pprime]
      simp only [a, sub_add_cancel, integrand]
    _ = _ := integral_add_right_eq_self integrand k0
