-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.mul_mem_UW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:29:53.123898+00:00
-- url     : https://prove2.me/submissions/8ed77ec1-ae5a-4d28-b6f1-7edb857d8f33

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_NilpotentSubgroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
theorem _root_.solution {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UWset k r z) (hb : b ∈ UWset k r z) : a * b ∈ UWset k r z := by
  simp only [UWset, UH, Set.mem_setOf_eq] at ha hb ⊢
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  refine ⟨?_, fun i => ⟨?_, ?_⟩, ?_⟩
  · rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [ha1, hb1]
  · rw [← Matrix.mulVec_mulVec, (hb2 i).1, (ha2 i).1]
  · rw [← Matrix.mulVec_mulVec, (hb2 i).2, (ha2 i).2]
  · rw [← Matrix.mulVec_mulVec, hb3, ha3]
end PI.QuotSetU.UnitaryGroupMassFormula.SW
