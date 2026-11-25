-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.area_cmL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:21.441333+00:00
-- url     : https://prove2.me/submissions/f590db9f-d48a-4f39-80f5-1a90352ac046

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NsmulRelIdxMem
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_cmL____a97a4aa1fba4
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UnitDetRoot_cmL____ed65171107ba
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
theorem _root_.solution : UnitDetRootDefs.area (UnitDetRootDefs.cmL a b d ha hd lam hlam) = Complex.normSq lam * a * (Real.sqrt d / 2) := by
  rw [UnitDetRootDefs.area, cmL_ω₁, cmL_ω₂]
  have hpos : 0 < Complex.normSq lam * a * (Real.sqrt d / 2) := by
    have h1 : 0 < Complex.normSq lam := Complex.normSq_pos.mpr hlam
    have h2 : (0 : ℝ) < a := by exact_mod_cast ha
    have h3 : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    positivity
  have e : (conj (lam * a) * (lam * UnitDetRootDefs.cmTheta b d)).im = Complex.normSq lam * a * (Real.sqrt d / 2) := by
    simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.natCast_re,
      Complex.natCast_im, theta_re', theta_im', Complex.normSq_apply, map_mul, map_natCast]
    ring
  rw [e, abs_of_pos hpos]
end PI.UnitaryGroupMassFormula.UnitDetRoot
