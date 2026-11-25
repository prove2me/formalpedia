-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.pair_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:26.347399+00:00
-- url     : https://prove2.me/submissions/981fb9e0-7932-457d-8307-0a1721606bfc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NsmulRelIdxMem
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_theta_re__fe5349d94a38
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_theta_im__25f4bf5b8973

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
variable {a : ℕ} {b : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution (p q p' q' : ℤ) :
    ((lam * ((p : ℂ) * a + (q : ℂ) * UnitDetRootDefs.cmTheta b d)) * conj (lam * ((p' : ℂ) * a + (q' : ℂ) * UnitDetRootDefs.cmTheta b d))).im
      = Complex.normSq lam * a * (Real.sqrt d / 2) * ((q * p' - p * q' : ℤ) : ℝ) := by
  simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
    Complex.intCast_re, Complex.intCast_im, Complex.natCast_re, Complex.natCast_im, theta_re', theta_im',
    Complex.normSq_apply, map_mul, map_add, map_intCast, map_natCast]
  push_cast
  ring
end PI.UnitaryGroupMassFormula.UnitDetRoot
