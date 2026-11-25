-- Prove2me | solution 1 for PI.VolNzeroOne.W.coord_zero_of_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:48:21.857379+00:00
-- url     : https://prove2.me/submissions/d794f209-b3ef-4fa2-a767-42e958fce654

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolNzeroOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NilpotentVolumeOne_LinearIndependentFrameWithNormal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolNzeroOne PI.VolNzeroOne.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace PI.VolNzeroOne.W
theorem _root_.solution {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (v : Fin n → E)
    (hv : Matrix.mulVec G v = 0) (k i : Fin n) (d : E) (hd : d ≠ 0)
    (hrow : ∀ j, G k j = if j = i then d else 0) : v i = 0 := by
  have h := congrFun hv k
  simp only [Matrix.mulVec, dotProduct, hrow, Pi.zero_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  exact (mul_eq_zero.mp h).resolve_left hd
end PI.VolNzeroOne.W
