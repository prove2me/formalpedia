-- Prove2me | solution 1 for PI.StabPairsW.uMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:39:37.23+00:00
-- url     : https://prove2.me/submissions/012eebc6-7705-4915-b659-ebbd63d7b7f4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Theorems.Thm_PI_StabPairsW_herm_es
import Theorems.Thm_PI_StabPairsW_herm_sum_left
import Theorems.Thm_PI_StabPairsW_fvec_eI
import Theorems.Thm_PI_StabPairsW_herm_Hpk_fvec_eq_ite
import Theorems.Thm_PI_StabPairsW_col_of_mul

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
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.StabPairsW
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (hz : StdZ k r z) (s : B.Mat k r)
    (x : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (h : s * Ff k r z = Ff k r z * x) : uMap k r z s = x := by
  obtain ⟨hzW, hT⟩ := hz
  ext a b
  have hcol := col_of_mul z s x h b
  simp only [uMap]
  split_ifs with ha
  · rw [hcol, herm_sum_left]
    simp_rw [herm_es, fvec_eI z hzW]
    rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hc
      have h2 : ¬ c.val = a.val := fun h2 => hc (Fin.ext h2)
      simp [h2]
    · simp
  · have heq : a = Fin.last r := Fin.ext (by have := a.isLt; simp; omega)
    have hne : herm (Hpk k r) z z ≠ 0 := by
      intro h0
      simp [Tz, h0] at hT
    rw [hcol, herm_sum_left]
    simp_rw [herm_Hpk_fvec_eq_ite z hzW]
    rw [Finset.sum_eq_single (Fin.last r)]
    · rw [if_pos rfl, heq, mul_div_assoc, div_self hne, mul_one]
    · intro c _ hc
      rw [if_neg hc, mul_zero]
    · simp
end PI.StabPairsW
