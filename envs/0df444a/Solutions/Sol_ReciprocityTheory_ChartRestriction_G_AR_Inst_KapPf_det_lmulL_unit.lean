-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf.det_lmulL_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:29:34.446467+00:00
-- url     : https://prove2.me/submissions/4345d8c3-8c79-4f02-831d-a02b65289979

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
theorem _root_.solution (N : Frame X.Ψ r) (hlow : ∀ τ a x, a < x → N τ a x = 0) (hdiag : ∀ τ a, N τ a a = 1) :
    LinearMap.det (lmulL X N) = 1 := by
  classical
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Ent X))]
  rw [det_of_blockDiag _ (fun e : Ent X => OrderDual.toDual e.2.1.1) (fun e e' hlt => by
      rw [lmulL_entry]
      split_ifs with h
      · exact hlow _ _ _ (by simpa using hlt)
      · rfl) (fun _ => 1) (fun e e' hk => by
      rw [lmulL_entry]
      have hk' : e.2.1.1 = e'.2.1.1 := by simpa using hk
      by_cases h : e = e'
      · subst h; simp [hdiag]
      · rw [if_neg h, if_neg]
        intro h2
        exact h ((ent_eq_iff X e e').2 ⟨h2.1, hk', h2.2⟩))]
  simp
end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
