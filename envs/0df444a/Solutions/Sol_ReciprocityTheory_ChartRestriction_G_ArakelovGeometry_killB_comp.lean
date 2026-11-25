-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.killB_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:54:33.132522+00:00
-- url     : https://prove2.me/submissions/5535902f-5f2a-4bd8-b026-584a30e9a245

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_HasympAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NotRelevantOfDimZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_killB_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {T T' : Finset K} (h : T ⊆ T') :
    (killB T' : MRing ι →ₐ[ℤ] MRing ι).comp (killB T) = killB T' := by
  apply MvPolynomial.algHom_ext
  intro p
  rw [AlgHom.comp_apply, killB_X]
  split_ifs with hp
  · rw [map_zero, killB_X, if_pos (h hp)]
  · rfl
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
