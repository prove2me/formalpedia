-- Prove2me | solution 1 for PI.QnWCellW.bigCell_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:20:06.041509+00:00
-- url     : https://prove2.me/submissions/6eacfff2-5ec9-480c-bd53-d6c71e0fe1fc

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylCellRange_ReflectionMultiplicationOnBigCell
import Theorems.Thm_PI_QnWCellW_cN_val
import Theorems.Thm_PI_QnWCellW_cN_mk
import Theorems.Thm_P2M_PI_QnWCellW__E_mk_406185e64600
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.QnWCellW.cN_val

set_option autoImplicit false
open Matrix Finset
open PI PI.QnWCellW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
namespace PI.QnWCellW
theorem _root_.solution (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (p q : Fin (2 * r + k + 1)) :
    bigCell k r c μ p q =
      if q.val < r then (if p.val = 2 * r + k - q.val then cN r c q.val else 0)
      else if q.val ≤ r + k then
        (if r ≤ p.val ∧ p.val ≤ r + k then μE μ (p.val - r) (q.val - r) else 0)
      else (if p.val = 2 * r + k - q.val then (star (cN r c (2 * r + k - q.val)))⁻¹ else 0) := by
  have hq := q.isLt
  simp only [bigCell]
  by_cases h1 : q.val < r
  · rw [dif_pos h1, if_pos h1, cN_mk r c q.val h1]
    have e : (p = esI k r ⟨q.val, h1⟩) ↔ p.val = 2 * r + k - q.val := by
      rw [Fin.ext_iff]
      rfl
    by_cases h : p.val = 2 * r + k - q.val
    · rw [if_pos (e.mpr h), if_pos h]
    · rw [if_neg (mt e.mp h), if_neg h]
  · rw [dif_neg h1, if_neg h1]
    by_cases h2 : q.val ≤ r + k
    · rw [dif_pos h2, if_pos h2]
      by_cases h3 : r ≤ p.val ∧ p.val ≤ r + k
      · rw [dif_pos h3, if_pos h3]
        exact μE_mk μ _ _ _ _
      · rw [dif_neg h3, if_neg h3]
    · rw [dif_neg h2, if_neg h2]
      have h4 : 2 * r + k - q.val < r := by omega
      rw [cN_mk r c _ h4]
end PI.QnWCellW
