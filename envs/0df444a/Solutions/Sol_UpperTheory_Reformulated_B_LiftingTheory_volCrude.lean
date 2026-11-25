-- Prove2me | solution 1 for UpperTheory.Reformulated.B.LiftingTheory.volCrude
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:14:10.993942+00:00
-- url     : https://prove2.me/submissions/77c38ac9-6fa3-4445-9ffd-d30f132db5c4

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapLeftMulVolumeEq
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapMulVolumeOfSubgroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftingTheory
import Theorems.Thm_UpperTheory_map_left_mul_volume_eq
import Theorems.Thm_UpperTheory_map_mul_volume_of_subgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix in
private theorem hpk_sq (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := by
  have key : ∀ i : Fin (2 * r + k + 1), ∃ s : Fin (2 * r + k + 1),
      (s.val = if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val) := fun i =>
    ⟨⟨if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val, by
      have := i.isLt; split_ifs <;> omega⟩, rfl⟩
  ext i l
  obtain ⟨s, hs⟩ := key i
  have hi := i.isLt
  have hl := l.isLt
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · simp only [Formalism.QuantumDeterminants.Hpk, Matrix.one_apply, Fin.ext_iff]
    split_ifs at hs ⊢ <;> first | omega | norm_num
  · intro j _ hj
    have hj' : j.val ≠ s.val := fun h => hj (Fin.ext h)
    have hjl := j.isLt
    have : Formalism.QuantumDeterminants.Hpk k r i j = 0 := by
      simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
      split_ifs at hs ⊢ <;> first | omega | rfl
    rw [this, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ s) h
open Matrix in
private theorem norm_det_one (k r : ℕ) (g : Formalism.FourierDecayAlt.B.Mat k r) (hg : g ∈ Formalism.FourierDecayAlt.B.GV k r) :
    ‖g.det‖ = 1 := by
  have h1 : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have h2 : (Formalism.QuantumDeterminants.Hpk k r).det ≠ 0 := by
    intro h
    have := congrArg Matrix.det (hpk_sq k r)
    rw [Matrix.det_mul, h, Matrix.det_one] at this
    simp at this
  have h3 := congrArg (fun m => ‖Matrix.det m‖) h1
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star] at h3
  have h4 : ‖(Formalism.QuantumDeterminants.Hpk k r).det‖ ≠ 0 := norm_ne_zero_iff.mpr h2
  have h5 : ‖g.det‖ * ‖g.det‖ = 1 := by
    apply mul_left_cancel₀ h4
    linarith
  have h6 := norm_nonneg g.det
  nlinarith
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.LiftingTheory
theorem _root_.solution :
    Formalism.FourierDecayAlt.B2.VolCrude := by
  intro k r μ h
  have hd : ∀ a ∈ (Formalism.FourierDecayAlt.B.GV k r : Set (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ)),
      ‖(Matrix.of a).det‖ = 1 := fun a ha => norm_det_one k r a ha
  obtain ⟨C, hC⟩ := UpperTheory.map_mul_volume_of_subgroup (2 * r + k + 1) (Formalism.FourierDecayAlt.B.GV k r) μ h.conc hd
    (fun a ha => UpperTheory.map_left_mul_volume_eq _ a (hd a ha)) (fun a ha => h.left a ha) h.finite_compact
  refine ⟨C, fun R hR => ?_⟩
  have e : R ^ (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) = R ^ (2 * (2 * r + k + 1) ^ 2) := by
    rw [← Real.rpow_natCast R]
    congr 1
    push_cast
    ring
  rw [e]
  exact hC R hR
end UpperTheory.Reformulated.B.LiftingTheory
