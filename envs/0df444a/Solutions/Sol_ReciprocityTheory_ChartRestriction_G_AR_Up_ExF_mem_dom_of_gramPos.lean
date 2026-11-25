-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.mem_dom_of_gramPos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:38:51.34008+00:00
-- url     : https://prove2.me/submissions/4eab3642-0242-41cb-b657-5eaf353dd1fe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_psgn_dmin_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_psgn_dmin_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_mem_dom_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
theorem _root_.solution {x : Frame X.Ψ r}
    (h : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ (X.gramPos x τ).PosDef) : x ∈ X.dom := by
  rw [Data.mem_dom_iff]
  intro τ
  refine ⟨(h τ).1, fun i => ?_⟩
  have hir := i.isLt
  by_cases hip : (i : ℕ) ≤ X.p0
  · exact psgn_dmin_le X τ (h τ).2 i hip
  · obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = X.p0 + k := ⟨(i : ℕ) - X.p0, by omega⟩
    exact psgn_dmin_gt X τ (h τ).1 (h τ).2 k (by omega) i hk
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
