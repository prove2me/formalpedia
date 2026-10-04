-- Prove2me | solution 1 for TeschlQM.Weyl.resolvent_sub_compact_forall
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:21:44.479673+00:00
-- url     : https://prove2.me/submissions/edb0344f-6700-40b5-ac4e-f26df9431e3b

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet

namespace TeschlQM.Weyl

open TeschlQM.Shared

/-- First resolvent identity: `R' = R + (z' - z) R R'` pointwise. -/
lemma resolvent_identity_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) {z z' : ℂ} {R R' : H →L[ℂ] H}
    (hR : IsResolventAt A z R) (hR' : IsResolventAt A z' R') (φ : H) :
    R' φ = R φ + (z' - z) • R (R' φ) := by
  obtain ⟨hψ, hAψ⟩ := hR'.1 φ
  have h2 := hR.2 ⟨R' φ, hψ⟩
  simp only at h2
  have hcalc : A ⟨R' φ, hψ⟩ - z • R' φ = φ + (z' - z) • R' φ := by
    have : A ⟨R' φ, hψ⟩ - z • R' φ = (A ⟨R' φ, hψ⟩ - z' • R' φ) + (z' - z) • R' φ := by
      rw [sub_smul]; abel
    rw [this, hAψ]
  rw [hcalc] at h2
  rw [map_add, map_smul] at h2
  exact h2.symm

/-- `R' = R * (1 + (z' - z) • R')` as continuous linear maps. -/
lemma resolvent_identity_mul_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) {z z' : ℂ} {R R' : H →L[ℂ] H}
    (hR : IsResolventAt A z R) (hR' : IsResolventAt A z' R') :
    R' = R * (1 + (z' - z) • R') := by
  ext φ
  rw [resolvent_identity_core A hR hR' φ]
  simp [ContinuousLinearMap.mul_apply]

/-- `R' = (1 + (z' - z) • R') * R` as continuous linear maps. -/
lemma resolvent_identity_mul_core' {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) {z z' : ℂ} {R R' : H →L[ℂ] H}
    (hR : IsResolventAt A z R) (hR' : IsResolventAt A z' R') :
    R' = (1 + (z' - z) • R') * R := by
  ext φ
  have h := resolvent_identity_core A hR' hR φ
  -- h : R φ = R' φ + (z - z') • R' (R φ)
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply]
  have h' : R' φ = R φ - (z - z') • R' (R φ) := eq_sub_of_add_eq h.symm
  rw [h', sub_smul, sub_smul]
  abel

end TeschlQM.Weyl

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B : H →ₗ.[ℂ] H)
    (h : ∃ (z : ℂ) (RA RB : H →L[ℂ] H), TeschlQM.Shared.IsResolventAt A z RA ∧ TeschlQM.Shared.IsResolventAt B z RB ∧
      IsCompactOperator (RA - RB)) :
    ∀ (z : ℂ) (RA RB : H →L[ℂ] H), TeschlQM.Shared.IsResolventAt A z RA → TeschlQM.Shared.IsResolventAt B z RB →
      IsCompactOperator (RA - RB) := by
  obtain ⟨z, RA, RB, hRA, hRB, hK⟩ := h
  intro z' RA' RB' hRA' hRB'
  set P : H →L[ℂ] H := 1 + (z' - z) • RA' with hP
  set Q : H →L[ℂ] H := 1 + (z' - z) • RB' with hQ
  have e1 : RA' = P * RA := TeschlQM.Weyl.resolvent_identity_mul_core' A hRA hRA'
  have e2 : RB' = RB * Q := TeschlQM.Weyl.resolvent_identity_mul_core B hRB hRB'
  have key : RA' - RB' = P * (RA - RB) * Q := by
    have : P * (RA - RB) * Q = P * RA * Q - P * RB * Q := by noncomm_ring
    rw [this, ← e1, mul_assoc, ← e2]
    -- RA' * Q - P * RB' ; expand: RA' + c RA' RB' - RB' - c RA' RB'
    simp only [hP, hQ, mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc]
    abel
  have hfun : (⇑(RA' - RB') : H → H) = ⇑P ∘ ⇑(RA - RB) ∘ ⇑Q := by
    rw [key]; ext φ; simp [ContinuousLinearMap.mul_apply]
  rw [hfun]
  exact (hK.comp_clm Q).clm_comp P

#print axioms solution
