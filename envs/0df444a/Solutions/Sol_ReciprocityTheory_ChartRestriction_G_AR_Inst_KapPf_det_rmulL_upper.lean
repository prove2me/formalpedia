-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf.det_rmulL_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:36:40.272716+00:00
-- url     : https://prove2.me/submissions/f628617e-7e46-479c-abad-4a379a7d25c3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetOfBlockDiag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_KapPf_det_of_blockDiag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_KapPf_ent_eq_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_KapPf_rmulL_entry

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
    LinearMap.det (rmulL X b) = ∏ e : Ent X, b e.1 e.2.1.2 e.2.1.2 := by
  classical
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Ent X))]
  exact det_of_blockDiag _ (fun e : Ent X => OrderDual.toDual e.2.1.2) (fun e e' hlt => by
      rw [rmulL_entry]
      split_ifs with h
      · exact hup _ _ _ (by simpa using hlt)
      · rfl) _ (fun e e' hk => by
      rw [rmulL_entry]
      have hk' : e.2.1.2 = e'.2.1.2 := by simpa using hk
      by_cases h : e = e'
      · subst h; simp
      · rw [if_neg h, if_neg]
        intro h2
        exact h ((ent_eq_iff X e e').2 ⟨h2.1, h2.2, hk'⟩))
end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
