-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P64.genericMedium_stationaryProfile
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T10:44:22.341291+00:00
-- url     : https://prove2.me/submissions/c28591e2-e944-480d-8faa-7f588ebab443

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

theorem AuxMS_dot (x y : Momentum) : momentumDot x y = inner ℝ x y := by
  simp [momentumDot, PiLp.inner_apply, mul_comm]

theorem AuxGM_perp (x Q : Momentum) : perpendicular x (-Q) = perpendicular x Q := by
  simp only [perpendicular, parallel, AuxMS_dot, inner_neg_right, norm_neg, smul_neg, neg_div,
    neg_smul, neg_neg]

theorem AuxGM_iso (F : TransverseFrames) (Q : Momentum) (hQ : Q ≠ 0) :
    ∃ G : Renew46.P04.Plane ℝ ≃ₗᵢ[ℝ] Renew46.P04.Plane ℝ, ∀ k, F.map Q (G k) = F.map (-Q) k := by
  have ho : ∀ k, momentumDot (F.map (-Q) k) Q = 0 := by
    intro k; have := F.orthogonal (-Q) k
    rw [AuxMS_dot] at this ⊢; rw [inner_neg_right] at this; linarith
  choose g hg using fun k => F.onto Q hQ (F.map (-Q) k) (ho k)
  have hinj := (F.map Q).injective
  let L : Renew46.P04.Plane ℝ →ₗ[ℝ] Renew46.P04.Plane ℝ :=
    { toFun := g
      map_add' := fun a b => hinj (by rw [map_add, hg, hg, hg, map_add])
      map_smul' := fun c a => hinj (by rw [map_smul, hg, hg, map_smul]; rfl) }
  let G : Renew46.P04.Plane ℝ →ₗᵢ[ℝ] Renew46.P04.Plane ℝ :=
    { toLinearMap := L
      norm_map' := fun k => by
        show ‖g k‖ = ‖k‖
        rw [← (F.map Q).norm_map, hg, (F.map (-Q)).norm_map] }
  exact ⟨G.toLinearIsometryEquiv rfl, fun k => hg k⟩

theorem AuxGM_avg (d : CollisionData) (F : TransverseFrames) (beta : ℝ)
    (hreciprocal : ∀ pf pi, crossSection d pf pi = crossSection d pi pf) (P Q : Momentum) :
    averagedCrossSection d F beta P (-Q) = averagedCrossSection d F beta P Q := by
  by_cases hQ : Q = 0
  · subst hQ; simp
  obtain ⟨G, hG⟩ := AuxGM_iso F Q hQ
  unfold averagedCrossSection transverseRelative
  simp only [AuxGM_perp, ← hG, smul_neg, sub_neg_eq_add]
  have h := (G.measurePreserving).integral_comp G.toHomeomorph.measurableEmbedding
    (fun k => maxwellPlane d.parameters.m beta (F.map Q k) *
      crossSection d (relativeMomentum d.parameters (perpendicular (F.map Q k) Q)
          (perpendicular P Q) - (1 / 2 : ℝ) • Q)
        (relativeMomentum d.parameters (perpendicular (F.map Q k) Q)
          (perpendicular P Q) + (1 / 2 : ℝ) • Q))
  rw [← h]
  congr 1; funext k
  rw [hreciprocal]
  rfl

theorem _root_.solution (d : CollisionData) (F : TransverseFrames)
    (beta : ℝ) (hbeta : 0 < beta) (S : Momentum → Momentum → ℝ)
    (hS : ∀ Q P, 0 ≤ S Q P)
    (hbalance : ∀ Q P, S Q P = Real.exp (-beta * energyTransfer d.parameters Q P) * S (-Q) (P + Q))
    (hreciprocal : ∀ pf pi, crossSection d pf pi = crossSection d pi pf)
    (hplane : ∀ P Q, Integrable (fun k : Renew46.P04.Plane ℝ =>
      maxwellPlane d.parameters.m beta (F.map Q k) * crossSection d
        (transverseRelative d.parameters (F.map Q k) P Q - (1 / 2 : ℝ) • Q)
        (transverseRelative d.parameters (F.map Q k) P Q + (1 / 2 : ℝ) • Q)))
    (P : Momentum)
    (hintegrable : Integrable (fun Q => averagedCrossSection d F beta P Q *
      (S Q (P - Q) * maxwell d.parameters.M beta (P - Q) -
        S Q P * maxwell d.parameters.M beta P))) :
    structureGenerator d F beta S (maxwell d.parameters.M beta) P = 0 := by
  have hM := d.parameters.M_pos
  set ν := maxwell d.parameters.M beta
  have hν : ∀ Q, ν (P + Q) = Real.exp (-beta * energyTransfer d.parameters Q P) * ν P := by
    intro Q
    simp only [ν, maxwell, energyTransfer, AuxMS_dot]
    rw [mul_left_comm, ← Real.exp_add, norm_add_sq_real]
    congr 2
    rw [real_inner_comm]
    field_simp
    ring
  set X : Momentum → ℝ := fun Q => S Q (P - Q) * ν (P - Q)
  have hY : ∀ Q, S Q P * ν P = X (-Q) := by
    intro Q
    simp only [X, sub_neg_eq_add]
    rw [hbalance Q P, hν]; ring
  set f : Momentum → ℝ := fun Q => averagedCrossSection d F beta P Q * (X Q - X (-Q))
  have hodd : ∀ Q, f (-Q) = -f Q := by
    intro Q; simp only [f, neg_neg, AuxGM_avg d F beta hreciprocal]; ring
  unfold structureGenerator
  have e : (fun Q => averagedCrossSection d F beta P Q * (S Q (P - Q) * ν (P - Q) - S Q P * ν P))
      = f := by
    funext Q; simp only [f]; rw [hY Q]
  rw [e]
  have h0 : ∫ Q, f Q = 0 := by
    have h1 : ∫ Q, f (-Q) = ∫ Q, f Q := integral_neg_eq_self f volume
    simp only [hodd, integral_neg] at h1
    linarith
  rw [h0, mul_zero]

end QAlgorithms.Papers.Independent.Intake100.P64

end
