-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf.det_lmulL_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:29:37.09471+00:00
-- url     : https://prove2.me/submissions/b9e2e07b-5527-4b99-a54e-c37ad9d86b42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetOfBlockDiag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_KapPf_det_of_blockDiag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_KapPf_ent_eq_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_KapPf_lmulL_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix
open scoped Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
theorem _root_.solution (b : Frame X.Ψ r) (hup : ∀ τ a x, x < a → b τ a x = 0) :
    LinearMap.det (lmulL X b) = ∏ e : Ent X, b e.1 e.2.1.1 e.2.1.1 := by
  classical
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Ent X))]
  exact det_of_blockDiag _ (fun e : Ent X => e.2.1.1) (fun e e' hlt => by
      rw [lmulL_entry]
      split_ifs with h
      · exact hup _ _ _ hlt
      · rfl) _ (fun e e' hk => by
      rw [lmulL_entry]
      by_cases h : e = e'
      · subst h; simp
      · rw [if_neg h, if_neg]
        intro h2
        exact h ((ent_eq_iff X e e').2 ⟨h2.1, hk, h2.2⟩))
end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
