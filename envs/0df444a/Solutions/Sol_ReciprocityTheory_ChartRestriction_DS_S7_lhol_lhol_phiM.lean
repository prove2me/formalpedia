-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.lhol_lhol_phiM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:58.667816+00:00
-- url     : https://prove2.me/submissions/4d628368-14a8-44fc-8f02-2c522ea0c90f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lhol_phiM_lower
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lhol_phiM_diag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_contDiffAt_phiM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_differentiableAt_phiM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_isOpen_omega
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lhol_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (μ : Fin n → ℤ) (a b : Fin n) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) :
    Lhol (Matrix.single a b 1) (Lhol (Matrix.single b a 1) (PhiM μ)) z =
      ((casCoef μ a b : ℝ) : ℂ) * PhiM μ z := by
  have hO : IsOpen (OmegaSet n) := isOpen_omega
  have hlow : ∀ a b : Fin n, b < a →
      Lhol (Matrix.single b a 1) (Lhol (Matrix.single a b 1) (PhiM μ)) z = 0 := by
    intro a b hab
    have hev : Lhol (Matrix.single a b (1 : ℂ)) (PhiM μ) =ᶠ[nhds z] fun _ => (0 : ℂ) := by
      filter_upwards [hO.mem_nhds hz] with w hw using lhol_phiM_lower μ hab hw
    show fderiv ℂ (Lhol (Matrix.single a b (1 : ℂ)) (PhiM μ)) z _ = 0
    rw [hev.fderiv_eq]
    simp
  have e1 := lhol_phiM_diag μ a hz
  have e2 := lhol_phiM_diag μ b hz
  unfold Lhol at e1 e2
  rcases lt_trichotomy a b with h | rfl | h
  · rw [hlow b a h, casCoef, if_neg h.ne, if_neg (not_lt.mpr h.le)]
    simp
  · have hev : Lhol (Matrix.single a a (1 : ℂ)) (PhiM μ) =ᶠ[nhds z] fun w => -(μ a : ℂ) * PhiM μ w := by
      filter_upwards [hO.mem_nhds hz] with w hw using lhol_phiM_diag μ a hw
    have hf : fderiv ℂ (fun w => -(μ a : ℂ) * PhiM μ w) z = -(μ a : ℂ) • fderiv ℂ (PhiM μ) z :=
      ((differentiableAt_phiM μ hz).hasFDerivAt.const_mul (-(μ a : ℂ))).fderiv
    show fderiv ℂ (Lhol (Matrix.single a a (1 : ℂ)) (PhiM μ)) z _ = _
    rw [hev.fderiv_eq]
    erw [hf]
    rw [_root_.smul_apply, smul_eq_mul, e1, casCoef, if_pos rfl, if_neg (lt_irrefl a)]
    push_cast
    ring
  · rw [lhol_comm (contDiffAt_phiM μ hz) _ _, hlow a b h]
    simp only [Matrix.single_mul_single_same, mul_one, sub_mul, map_sub]
    rw [e1, e2, casCoef, if_neg h.ne', if_pos h]
    push_cast
    ring
end ReciprocityTheory.ChartRestriction.DS.S7
