-- Prove2me | solution 1 for P2M_PI_PolynomialProperness_CB_isUnit_det_monomialMatrix__59e50fe8fbb4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:48:21.426796+00:00
-- url     : https://prove2.me/submissions/bc5cbea6-26f4-40b7-a5cf-ee8ad76ff00b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_SecondOrderNormBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.CB
namespace PI.PolynomialProperness.CB
theorem _root_.solution {m : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) :
    IsUnit (monoP w d).det := by
  have hQ : monoP w d * monoP w.symm (fun j => (d (w.symm j))⁻¹) = 1 := by
    ext i j
    simp only [monoP, mul_apply, of_apply, one_apply]
    rw [Finset.sum_eq_single (w.symm j)]
    · simp only [if_true, Equiv.apply_symm_apply]
      split_ifs with h
      · exact mul_inv_cancel₀ (hd _)
      · exact zero_mul _
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact isUnit_det_of_right_inverse hQ
end PI.PolynomialProperness.CB
