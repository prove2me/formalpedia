-- Prove2me | solution 1 for PI.GGConvScalarW.superdiag_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:40:38.034722+00:00
-- url     : https://prove2.me/submissions/771a2f47-69c1-495a-9cbc-9441867b626f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
noncomputable section
open Classical
open PI PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ}
namespace PI.GGConvScalarW
theorem _root_.solution {A B : Matrix (Fin k) (Fin k) F} (hA : IsUTm A) (hB : IsUTm B) :
    superdiag k (A * B) = superdiag k A + superdiag k B := by
  have key : ∀ i j : Fin k, (j : ℕ) = (i : ℕ) + 1 → (A * B) i j = A i j + B i j := by
    intro i j hj
    have hij : i ≠ j := fun h => by rw [h] at hj; omega
    rw [Matrix.mul_apply, Finset.sum_eq_add i j hij]
    · rw [hA.1, hB.1, one_mul, mul_one, add_comm]
    · intro c _ hc
      have h1 : (c : ℕ) ≠ i := fun h => hc.1 (Fin.ext h)
      have h2 : (c : ℕ) ≠ j := fun h => hc.2 (Fin.ext h)
      rcases Nat.lt_or_gt_of_ne h1 with h | h
      · rw [hA.2 i c (Fin.lt_iff_val_lt_val.2 h), zero_mul]
      · rw [hB.2 c j (Fin.lt_iff_val_lt_val.2 (by omega)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
    · intro h
      exact absurd (Finset.mem_univ _) h
  unfold superdiag
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · exact key i j hj
  · simp
end PI.GGConvScalarW
