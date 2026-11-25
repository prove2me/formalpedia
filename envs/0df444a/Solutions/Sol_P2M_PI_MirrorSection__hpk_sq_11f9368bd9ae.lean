-- Prove2me | solution 1 for P2M_PI_MirrorSection__hpk_sq_11f9368bd9ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:02:29.523401+00:00
-- url     : https://prove2.me/submissions/88249749-7646-4fa9-83ab-d72030e8280c

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI

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
open PI PI.MirrorSection₂
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.MirrorSection₂
theorem _root_.solution (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  let t : Fin (2 * r + k + 1) :=
    ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩
  rw [Finset.sum_eq_single t]
  · simp only [Hpk, t, Fin.ext_iff]
    split_ifs <;> first | omega | norm_num
  · intro l _ hl
    have hl' : l.val ≠ t.val := fun h => hl (Fin.ext h)
    simp only [t] at hl'
    simp only [Hpk, Fin.ext_iff]
    split_ifs at hl' ⊢ <;> first | omega | norm_num
  · simp
end PI.MirrorSection₂
