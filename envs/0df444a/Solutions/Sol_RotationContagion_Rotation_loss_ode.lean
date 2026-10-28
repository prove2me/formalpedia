-- Prove2me | solution 1 for RotationContagion.Rotation.loss_ode
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:26:42.09324+00:00
-- url     : https://prove2.me/submissions/f4c0ff46-82d3-4a8b-a6ad-b4427fcda05a

import Mathlib
import Definitions.Def_RotationContagion_Rotation_Model

open RotationContagion.Rotation in
theorem solution (P : Params) (hP : P.Standing) :
    loss P 0 = 1 / P.K ∧
      ∀ t : ℝ, HasDerivAt (loss P) (P.γ * loss P t * (1 - loss P t)) t := by
  obtain ⟨hγ, hK, _⟩ := hP
  constructor
  · unfold loss b
    have h1 : P.γ * (0 - Real.log (P.K - 1) / P.γ) = -Real.log (P.K - 1) := by
      field_simp
      ring
    rw [h1, Real.exp_neg, Real.exp_log (by linarith)]
    have h2 : P.K - 1 ≠ 0 := by linarith
    have h3 : P.K ≠ 0 := by linarith
    field_simp
    ring_nf
    try simp [h3]
  · intro t
    have hz := ((hasDerivAt_id' t).sub_const (b P)).const_mul P.γ
    have he := hz.exp
    have hpos : (1 + Real.exp (P.γ * (t - b P))) ≠ 0 := by positivity
    have hd := he.div (he.const_add 1) hpos
    show HasDerivAt (fun t => Real.exp (P.γ * (t - b P)) / (1 + Real.exp (P.γ * (t - b P)))) _ t
    refine hd.congr_deriv ?_
    unfold loss
    field_simp
    try ring
