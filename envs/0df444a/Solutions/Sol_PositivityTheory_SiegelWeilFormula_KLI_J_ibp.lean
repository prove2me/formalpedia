-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KLI.J_ibp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:55:34.252579+00:00
-- url     : https://prove2.me/submissions/18ac0e72-8b3a-47f4-9799-a600f76e1695

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_intg_pow_quad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KLI
namespace PositivityTheory.SiegelWeilFormula.KLI
theorem _root_.solution {b : ℂ} (hb : b.re < 0) (k : ℕ) (c : ℂ) :
    2 * b * J b (k + 1) c + c * J b k c = -((k : ℂ) * J b (k - 1) c) := by
  have hu : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (y : ℂ) ^ k) ((k : ℂ) * (x : ℂ) ^ (k - 1)) x := fun x =>
    (hasDerivAt_pow k (x : ℂ)).comp_ofReal
  have hv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => cexp (b * (y : ℂ) ^ 2 + c * y))
      (cexp (b * (x : ℂ) ^ 2 + c * x) * (b * (2 * (x : ℂ)) + c)) x := by
    intro x
    have h0 : HasDerivAt (fun y : ℂ => b * y ^ 2 + c * y) (b * (2 * (x : ℂ)) + c) (x : ℂ) := by
      have h := ((hasDerivAt_pow 2 (x : ℂ)).const_mul b).add ((hasDerivAt_id (x : ℂ)).const_mul c)
      have e : b * (((2 : ℕ) : ℂ) * (x : ℂ) ^ (2 - 1)) + c * 1 = b * (2 * (x : ℂ)) + c := by push_cast; ring
      rw [e] at h
      exact h
    exact h0.comp_ofReal.cexp
  have I1 := intg_pow_quad hb (k + 1) c
  have I0 := intg_pow_quad hb k c
  have Im := intg_pow_quad hb (k - 1) c
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun y : ℝ => (y : ℂ) ^ k)
    (v := fun y : ℝ => cexp (b * (y : ℂ) ^ 2 + c * y))
    (u' := fun x : ℝ => (k : ℂ) * (x : ℂ) ^ (k - 1))
    (v' := fun x : ℝ => cexp (b * (x : ℂ) ^ 2 + c * x) * (b * (2 * (x : ℂ)) + c))
    (fun x _ => hu x) (fun x _ => hv x) ?_ ?_ I0
  · have e1 : ∀ x : ℝ, (x : ℂ) ^ k * (cexp (b * (x : ℂ) ^ 2 + c * x) * (b * (2 * (x : ℂ)) + c)) =
        (2 * b) * ((x : ℂ) ^ (k + 1) * cexp (b * (x : ℂ) ^ 2 + c * x)) +
          c * ((x : ℂ) ^ k * cexp (b * (x : ℂ) ^ 2 + c * x)) := fun x => by ring
    have e2 : ∀ x : ℝ, (k : ℂ) * (x : ℂ) ^ (k - 1) * cexp (b * (x : ℂ) ^ 2 + c * x) =
        (k : ℂ) * ((x : ℂ) ^ (k - 1) * cexp (b * (x : ℂ) ^ 2 + c * x)) := fun x => by ring
    beta_reduce at key
    simp_rw [e1, e2] at key
    rw [integral_add (I1.const_mul _) (I0.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul] at key
    simpa [J] using key
  · have : (fun y : ℝ => (y : ℂ) ^ k) * (fun x : ℝ => cexp (b * (x : ℂ) ^ 2 + c * x) * (b * (2 * (x : ℂ)) + c)) =
        fun x : ℝ => (2 * b) * ((x : ℂ) ^ (k + 1) * cexp (b * (x : ℂ) ^ 2 + c * x)) +
          c * ((x : ℂ) ^ k * cexp (b * (x : ℂ) ^ 2 + c * x)) := by
      funext x; simp only [Pi.mul_apply]; ring
    rw [this]; exact (I1.const_mul _).add (I0.const_mul _)
  · have : (fun x : ℝ => (k : ℂ) * (x : ℂ) ^ (k - 1)) * (fun y : ℝ => cexp (b * (y : ℂ) ^ 2 + c * y)) =
        fun x : ℝ => (k : ℂ) * ((x : ℂ) ^ (k - 1) * cexp (b * (x : ℂ) ^ 2 + c * x)) := by
      funext x; simp only [Pi.mul_apply]; ring
    rw [this]; exact Im.const_mul _
end PositivityTheory.SiegelWeilFormula.KLI
