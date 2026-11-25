-- Prove2me | solution 1 for PI.HookLower.diagHom_lpMinor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:42:58.976285+00:00
-- url     : https://prove2.me/submissions/47f2732d-a92b-4230-ba76-e10a719606b1

import Definitions.Def_Formalism_PeriodIntegrals_HookBound
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DiagonalMonomialFactorial
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
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookLower
namespace PI.HookLower
theorem _root_.solution {N : ℕ} (s : ℕ) (hr hn : s ≤ N) :
    diagHom N (lpMinor ℚ s hr hn) = monomial (diagMono s hr) 1 := by
  classical
  rw [lpMinor, AlgHom.map_det]
  have hM : (diagHom N).mapMatrix
      (Matrix.of fun p q : Fin s => (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin N × Fin N) ℚ)) =
      Matrix.diagonal fun p : Fin s => (X (Fin.castLE hr p, Fin.castLE hr p) : MvPolynomial (Fin N × Fin N) ℚ) := by
    ext p q
    by_cases hpq : p = q
    · subst hpq
      simp [diagHom]
    · have : ¬ (Fin.castLE hr p = Fin.castLE hn q) := by
        intro h
        apply hpq
        exact Fin.ext (by simpa [Fin.ext_iff] using h)
      simp [diagHom, hpq, this]
  rw [hM, Matrix.det_diagonal, diagMono, monomial_sum_one]
  rfl
end PI.HookLower
