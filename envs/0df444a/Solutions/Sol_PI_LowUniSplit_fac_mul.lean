-- Prove2me | solution 1 for PI.LowUniSplit.fac_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:18:57.009033+00:00
-- url     : https://prove2.me/submissions/22c2db1a-a646-46d2-a224-a8544a2860f3

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerUnipotentSplit_SecondFactorMemLowerTriangular
import Theorems.Thm_PI_LowUniSplit_mul_lt_zero
import Theorems.Thm_PI_LowUniSplit_mul_diag
import Theorems.Thm_PI_LowUniSplit_mul_below
import Theorems.Thm_PI_LowUniSplit_xs_eq
import Theorems.Thm_PI_LowUniSplit_first_factor_mem_lower_triangular
import Theorems.Thm_PI_LowUniSplit_second_factor_mem_lower_triangular

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
open PI PI.LowUniSplit
open Formalism.FourierDecayAlt.C2
variable {m : ℕ}
variable (S : Fin m → Fin m → Prop) [DecidableRel S] (l : Matrix (Fin m) (Fin m) ℂ)
namespace PI.LowUniSplit
theorem _root_.solution (hl : l ∈ LTset m) : fac1 S l * fac2 S l = l := by
  ext i j
  rcases lt_trichotomy i j with h | h | h
  · rw [mul_lt_zero (first_factor_mem_lower_triangular S l) (second_factor_mem_lower_triangular S l) h, hl.1 i j h]
  · subst h; rw [mul_diag (first_factor_mem_lower_triangular S l) (second_factor_mem_lower_triangular S l), hl.2]
  · rw [mul_below (first_factor_mem_lower_triangular S l) (second_factor_mem_lower_triangular S l) h]
    have e : ∀ k : Btw i j, fac1 S l i k.1 * fac2 S l k.1 j =
        (if S i k.1 then xs S l i k.1 else 0) * (if S k.1 j then 0 else xs S l k.1 j) := by
      intro k
      simp [fac1, fac2, ne_of_gt k.2.2, ne_of_gt k.2.1, k.2.1, k.2.2]
    rw [Finset.sum_congr rfl (fun k _ => e k)]
    have : fac1 S l i j + fac2 S l i j = xs S l i j := by
      by_cases hs : S i j <;> simp [fac1, fac2, ne_of_gt h, h, hs]
    rw [this, xs_eq]
    ring
end PI.LowUniSplit
