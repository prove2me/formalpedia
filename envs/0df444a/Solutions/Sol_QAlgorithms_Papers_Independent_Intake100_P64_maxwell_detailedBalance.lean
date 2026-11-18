-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P64.maxwell_detailedBalance
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-11-18T02:12:34.126407+00:00
-- url     : https://prove2.me/submissions/08c960cd-4c98-4849-a919-2aad22a2c3c9

import Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_collisionCoefficient_classicalCompatibility

noncomputable section

open MeasureTheory Filter
open QAlgorithms.Papers.Independent.Intake100.P64
open scoped BigOperators ENNReal NNReal Topology

local notation "Plane" => QAlgorithms.Papers.Independent.Renew46.P04.Plane ℝ

private theorem dot_eq_inner (x y : Momentum) : momentumDot x y = inner ℝ x y := by
  simp only [momentumDot, PiLp.inner_apply, Real.inner_apply]

private def frameToPlane (F : TransverseFrames) (Q R : Momentum) (hR : R ≠ 0)
    (horth : ∀ p, momentumDot p R = 0 ↔ inner ℝ Q p = 0) :
    Plane ≃ₗᵢ[ℝ] (innerSL ℝ Q).ker :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (F.map R).toLinearMap.codRestrict _
        (fun k => (horth _).mp (F.orthogonal R k))
      norm_map' := (F.map R).norm_map }
    (by
      intro p
      obtain ⟨k, hk⟩ := F.onto R hR p ((horth p).mpr p.property)
      exact ⟨k, Subtype.ext hk⟩)

private theorem change_frame (F : TransverseFrames) (Q : Momentum) (hQ : Q ≠ 0) :
    ∃ e : Plane ≃ₗᵢ[ℝ] Plane, ∀ k, F.map (-Q) (e k) = F.map Q k := by
  let f := frameToPlane F Q Q hQ (fun p => by rw [dot_eq_inner, real_inner_comm p Q])
  let g := frameToPlane F Q (-Q) (neg_ne_zero.mpr hQ) (fun p => by
    rw [dot_eq_inner, inner_neg_right, neg_eq_zero, real_inner_comm p Q])
  refine ⟨f.trans g.symm, fun k => ?_⟩
  have he := congrArg Subtype.val (g.apply_symm_apply (f k))
  exact he

private theorem parallel_neg' (P Q : Momentum) : parallel P (-Q) = parallel P Q := by
  simp [parallel, dot_eq_inner, inner_neg_right, neg_div, neg_smul]

private theorem parallel_add_self (P Q : Momentum) (hQ : Q ≠ 0) :
    parallel (P + Q) Q = parallel P Q + Q := by
  unfold parallel
  rw [dot_eq_inner, inner_add_left, real_inner_self_eq_norm_sq, add_div,
    div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr hQ)), add_smul, one_smul, dot_eq_inner]

private theorem outgoing_eq_rate (d : CollisionData) (F : TransverseFrames) (P Q : Momentum) :
    outgoingIntensity d F P Q = transferRate d F P Q := by
  unfold outgoingIntensity transferRate
  apply integral_congr_ae
  filter_upwards with k
  rw [collisionCoefficient_classicalCompatibility]
  unfold rateIntegrand
  ring

private theorem maxwell_tilt (mass beta : ℝ) (x y : Momentum) (t : ℝ)
    (hm : mass ≠ 0) (h : ‖x‖ ^ 2 - ‖y‖ ^ 2 = 2 * mass * t) :
    maxwell mass beta x = maxwell mass beta y * Real.exp (-beta * t) := by
  unfold maxwell
  rw [mul_assoc _ (Real.exp _) (Real.exp _), ← Real.exp_add]
  congr 2
  field_simp
  linear_combination -beta * h

private theorem rate_flip (d : CollisionData) (F : TransverseFrames) (beta : ℝ)
    (hgas : ∀ p, d.gas.value p = maxwell d.parameters.m beta p)
    (hreciprocal : ∀ pf pi, crossSection d pf pi = crossSection d pi pf)
    (P Q : Momentum) :
    transferRate d F P Q =
      transferRate d F (P + Q) (-Q) * Real.exp (-beta * energyTransfer d.parameters Q P) := by
  by_cases hQ : Q = 0
  · subst Q
    simp [transferRate, rateIntegrand, prefactor]
  obtain ⟨e, he⟩ := change_frame F Q hQ
  let a := d.parameters
  have hm := a.m_pos.ne'
  have hM := a.M_pos.ne'
  have hmM : a.m + a.M ≠ 0 := (add_pos a.m_pos a.M_pos).ne'
  have hred : a.m / (2 * reducedMass a) + a.m / (2 * reducedMass a) =
      1 + a.m / a.M := by
    unfold reducedMass
    field_simp
    <;> ring
  have hpar := parallel_add_self P Q hQ
  have hperp (p : Momentum) : perpendicular p (-Q) = perpendicular p Q := by
    rw [perpendicular, perpendicular, parallel_neg']
  have hPperp : perpendicular (P + Q) (-Q) = perpendicular P Q := by
    rw [hperp, perpendicular, perpendicular, hpar]
    abel
  have hpre : prefactor a (-Q) = prefactor a Q := by
    simp [prefactor, hQ, neg_ne_zero.mpr hQ, norm_neg]
  have hp : ∀ k, rateIntegrand d F P Q k =
      rateIntegrand d F (P + Q) (-Q) (e k) * Real.exp (-beta * energyTransfer a Q P) := by
    intro k
    let p := F.map Q k
    have hpk : momentumDot p Q = 0 := F.orthogonal Q k
    have hperpp : perpendicular p Q = p := by simp [perpendicular, parallel, hpk]
    have hgasrev : gasArgument a p (P + Q) (-Q) = gasArgument a p P Q - Q := by
      rw [gasArgument, gasArgument, hperp, parallel_neg', hpar, smul_neg, smul_add]
      match_scalars <;> first | ring1 | (unfold reducedMass; field_simp [hm, hM, hmM] <;> ring)
    have hdot : inner ℝ (gasArgument a p P Q) Q =
        (a.m / (2 * reducedMass a)) * ‖Q‖ ^ 2 + (a.m / a.M) * momentumDot P Q := by
      have hpk' : inner ℝ p Q = 0 := (dot_eq_inner _ _).symm ▸ hpk
      unfold gasArgument
      rw [hperpp]
      simp only [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hpk', zero_add]
      congr 1
      unfold parallel
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq,
        div_mul_cancel₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hQ))]
    have hnormdiff : ‖gasArgument a p P Q‖ ^ 2 -
        ‖gasArgument a p (P + Q) (-Q)‖ ^ 2 = 2 * a.m * energyTransfer a Q P := by
      rw [hgasrev, norm_sub_sq_real, hdot, energyTransfer, dot_eq_inner P Q,
        dot_eq_inner Q P, real_inner_comm P Q]
      calc
        _ = ((a.m / (2 * reducedMass a) + a.m / (2 * reducedMass a)) - 1) * ‖Q‖ ^ 2 +
            (a.m / a.M) * (inner ℝ P Q) * 2 := by ring
        _ = _ := by rw [hred]; ring
    have hmu : d.gas.value (gasArgument a p P Q) =
        d.gas.value (gasArgument a p (P + Q) (-Q)) * Real.exp (-beta * energyTransfer a Q P) := by
      rw [hgas, hgas]
      exact maxwell_tilt a.m beta _ _ _ hm hnormdiff
    have hrel : transverseRelative a p (P + Q) (-Q) = transverseRelative a p P Q := by
      rw [transverseRelative, transverseRelative, hPperp, hperp]
    unfold rateIntegrand
    rw [he k]
    change prefactor a Q * d.gas.value (gasArgument a p P Q) * _ =
      prefactor a (-Q) * d.gas.value (gasArgument a p (P + Q) (-Q)) * _ * _
    rw [hpre, hrel, hmu, smul_neg, sub_neg_eq_add, ← sub_eq_add_neg,
      hreciprocal (transverseRelative a p P Q + (1 / 2 : ℝ) • Q)
        (transverseRelative a p P Q - (1 / 2 : ℝ) • Q)]
    ring
  unfold transferRate
  rw [← integral_mul_const]
  calc
    _ = ∫ k, rateIntegrand d F (P + Q) (-Q) (e k) *
        Real.exp (-beta * energyTransfer a Q P) :=
      integral_congr_ae (Eventually.of_forall hp)
    _ = _ := by
      let integrand (k : Plane) :=
        rateIntegrand d F (P + Q) (-Q) k * Real.exp (-beta * energyTransfer a Q P)
      change (∫ k, integrand (e k) ∂(volume : Measure Plane)) =
        ∫ k, integrand k ∂(volume : Measure Plane)
      exact e.measurePreserving.integral_comp e.toMeasurableEquiv.measurableEmbedding integrand

theorem solution (d : CollisionData) (F : TransverseFrames)
    (beta : ℝ) (hbeta : 0 < beta)
    (hgas : ∀ p, d.gas.value p = maxwell d.parameters.m beta p)
    (hreciprocal : ∀ pf pi, crossSection d pf pi = crossSection d pi pf)
    (hplane : ∀ P Q, Integrable (rateIntegrand d F P Q)) :
    (∀ P Q, transferRate d F P Q = transferRate d F (P + Q) (-Q) *
      Real.exp (-beta * energyTransfer d.parameters Q P)) ∧
    (∀ P, Integrable (fun Q => transferRate d F (P - Q) Q *
        maxwell d.parameters.M beta (P - Q)) →
      Integrable (outgoingIntensity d F P) →
      classicalGenerator d F (maxwell d.parameters.M beta) P = 0) := by
  refine ⟨rate_flip d F beta hgas hreciprocal, ?_⟩
  intro P _ _
  let a := d.parameters
  let nu := maxwell a.M beta
  have hin (Q : Momentum) :
      transferRate d F (P - Q) Q * nu (P - Q) = outgoingIntensity d F P (-Q) * nu P := by
    have hflip := rate_flip d F beta hgas hreciprocal (P - Q) Q
    rw [sub_add_cancel] at hflip
    have hnorm : ‖P‖ ^ 2 - ‖P - Q‖ ^ 2 = 2 * a.M * energyTransfer a Q (P - Q) := by
      calc
        _ = ‖P - Q + Q‖ ^ 2 - ‖P - Q‖ ^ 2 := by rw [sub_add_cancel]
        _ = _ := by
          rw [norm_add_sq_real, energyTransfer, dot_eq_inner, ← real_inner_comm Q (P - Q)]
          field_simp [a.M_pos.ne']
          <;> ring
    have hnu := maxwell_tilt a.M beta P (P - Q) (energyTransfer a Q (P - Q))
      a.M_pos.ne' hnorm
    change nu P = nu (P - Q) * Real.exp (-beta * energyTransfer a Q (P - Q)) at hnu
    rw [hflip, outgoing_eq_rate, hnu]
    ring
  unfold classicalGenerator collisionLossRate
  change (∫ Q, transferRate d F (P - Q) Q * nu (P - Q)) -
      (∫ Q, outgoingIntensity d F P Q) * nu P = 0
  rw [← integral_mul_const, sub_eq_zero]
  calc
    _ = ∫ Q, outgoingIntensity d F P (-Q) * nu P :=
      integral_congr_ae (Eventually.of_forall hin)
    _ = _ := integral_neg_eq_self (fun Q => outgoingIntensity d F P Q * nu P) volume
