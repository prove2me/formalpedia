-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.rhF_eq_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:06:04.202991+00:00
-- url     : https://prove2.me/submissions/0cc2a12c-d1e7-4c9b-bddb-dc7fbfe683b0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_mem_OmF_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_rhF_eq_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
open NumberField Complex Matrix Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
open scoped ComplexConjugate ComplexOrder ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
theorem _root_.solution (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {y : V (nd X)} (hy : y ∈ OmF X x0) :
    rhF X x0 y = -Real.log (∏ τ, (Am X y τ).det.re) := by
  have key : ∀ τ, 0 < (Am X y τ).det.re ∧ ‖(Am X y τ).det‖ = (Am X y τ).det.re := by
    intro τ
    have hpos := ((mem_OmF_iff X x0 ho y).1 hy τ).det_pos
    have h := Complex.lt_def.1 hpos
    simp only [Complex.zero_re, Complex.zero_im] at h
    refine ⟨h.1, ?_⟩
    rw [show (Am X y τ).det = ((Am X y τ).det.re : ℂ) from Complex.ext (by simp) (by simp [← h.2])]
    rw [Complex.norm_real, Complex.ofReal_re, Real.norm_of_nonneg h.1.le]
  rw [rhF_eq_sum X x0 ho y, Real.log_prod (fun τ _ => (key τ).1.ne')]
  congr 1
  exact Finset.sum_congr rfl fun τ _ => by rw [(key τ).2]
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
