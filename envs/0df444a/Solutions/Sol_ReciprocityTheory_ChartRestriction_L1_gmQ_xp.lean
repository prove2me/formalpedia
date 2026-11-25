-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.gmQ_xp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:49:06.48907+00:00
-- url     : https://prove2.me/submissions/ebadb2e6-f9a3-4f98-83a3-973947ea309d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalMF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFacSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGmForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGmQ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_prodSer_conv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_prodSer_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_xp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_conv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_ev_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_eq_of_ev_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ev_xp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_gmForm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {m : ℕ} (hm : 0 < m) : xp m (qExpansion 1 (Gm m)) = prodSer m := by
  have hm0 : m ≠ 0 := hm.ne'
  have hF := gmForm hm
  refine eq_of_ev_eq (hF.conv.xp hm0) (prodSer_conv hm) ?_
  intro x hx0 hx1
  rw [ev_xp _ hm0]
  have hxne : x ≠ 0 := norm_pos_iff.mp hx0
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog : Real.log ‖x‖ < 0 := Real.log_neg hx0 hx1

  let w : ℂ := ⟨(m : ℝ) * Complex.arg x / (2 * Real.pi), -((m : ℝ) * Real.log ‖x‖) / (2 * Real.pi)⟩
  have him : 0 < w.im := by
    show 0 < -((m : ℝ) * Real.log ‖x‖) / (2 * Real.pi)
    apply div_pos _ (by positivity)
    nlinarith
  let τ : ℍ := ⟨w, him⟩
  have hτ : (τ : ℂ) = w := rfl
  have hlogx : 2 * (Real.pi : ℂ) * Complex.I * w / (m : ℂ) = Complex.log x := by
    apply Complex.ext
    · rw [Complex.div_natCast_re, Complex.log_re]
      simp [w]
      field_simp
    · rw [Complex.div_natCast_im, Complex.log_im]
      simp [w]
      field_simp
  have hq : qm m τ = x := by
    unfold qm
    rw [hτ, hlogx, Complex.exp_log hxne]
  have hq1 : qm 1 τ = x ^ m := by
    rw [← hq]
    unfold qm
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [← hq1, hF.ev_eq τ, ← prodSer_ev hm τ, hq]
end ReciprocityTheory.ChartRestriction.L1
