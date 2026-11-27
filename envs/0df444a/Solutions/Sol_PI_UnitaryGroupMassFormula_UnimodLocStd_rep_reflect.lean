-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_reflect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:18:02.964784+00:00
-- url     : https://prove2.me/submissions/dc924d0a-37c4-43d2-a653-6e7f7b814fc4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepBasic
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_H_re

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (f w : m → ℂ) (hz : stdH L m (f - w) (f - w) ≠ 0) :
    stdH L m (w + ((((stdH L m w w).re - (stdH L m f f).re) / (stdH L m (f - w) (f - w)).re : ℝ) : ℂ) • (f - w))
      (w + ((((stdH L m w w).re - (stdH L m f f).re) / (stdH L m (f - w) (f - w)).re : ℝ) : ℂ) • (f - w)) =
      stdH L m f f := by
  set H := stdH L m
  set t : ℝ := ((H w w).re - (H f f).re) / (H (f - w) (f - w)).re with ht_def
  have htC : (t : ℂ) = (H w w - H f f) / H (f - w) (f - w) := by
    rw [ht_def, Complex.ofReal_div, Complex.ofReal_sub, rep_H_re, rep_H_re, rep_H_re]
  have hconj : conj (t : ℂ) = t := Complex.conj_ofReal t
  have e1 : H (w + (t : ℂ) • (f - w)) (w + (t : ℂ) • (f - w)) =
      H w w + t * (H w f - H w w) + t * (H f w - H w w) + t * t * H (f - w) (f - w) := by
    simp only [map_add, map_smul, map_sub, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      map_smulₛₗ, smul_eq_mul, hconj]
    ring
  have hNz : H (f - w) (f - w) = H f f - H f w - H w f + H w w := by
    simp only [map_sub, LinearMap.sub_apply]; ring
  have ht : (t : ℂ) * H (f - w) (f - w) = H w w - H f f := by
    rw [htC, div_mul_cancel₀ _ hz]
  rw [e1]
  linear_combination ((t : ℂ) - 1) * ht + (t : ℂ) * hNz
end PI.UnitaryGroupMassFormula.UnimodLocStd
