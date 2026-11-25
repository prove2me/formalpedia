-- Prove2me | solution 1 for PI.WGB.pivotA_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:06:07.404906+00:00
-- url     : https://prove2.me/submissions/128029d9-96af-4001-b63e-cdd624d602d6

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_StepACleared
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.GradedWeylDivisibility MvPolynomial
variable {n : ℕ}
namespace PI.WGB
theorem _root_.solution (k : ℕ) (hk : k < n) (y : Fin (n + 1) × Fin (n + 1) → ℂ)
    (hy : clearedA k y) (hd : eval y (lpMinor ℂ (k + 1) (by omega) (by omega) :
      MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) ≠ 0) :
    y (⟨k, by omega⟩, ⟨k, by omega⟩) ≠ 0 := by
  unfold lpMinor at hd
  rw [RingHom.map_det] at hd
  have hM : (eval y).mapMatrix (Matrix.of fun p q : Fin (k + 1) =>
      (X (Fin.castLE (show k + 1 ≤ n + 1 by omega) p, Fin.castLE (show k + 1 ≤ n + 1 by omega) q) :
        MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)) =
      Matrix.diagonal (fun p => y (Fin.castLE (show k + 1 ≤ n + 1 by omega) p,
        Fin.castLE (show k + 1 ≤ n + 1 by omega) p)) := by
    ext p q
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, eval_X,
      Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rfl
    · have hpq : p.val ≠ q.val := fun e => h (Fin.ext e)
      have := p.isLt
      have := q.isLt
      apply hy
      · simp only [Fin.val_castLE]; omega
      · simpa using hpq
      · simp only [Fin.val_castLE]; omega
  rw [hM, Matrix.det_diagonal] at hd
  have := Finset.prod_ne_zero_iff.mp hd (Fin.last k) (Finset.mem_univ _)
  convert this using 3 <;> ext <;> simp
end PI.WGB
