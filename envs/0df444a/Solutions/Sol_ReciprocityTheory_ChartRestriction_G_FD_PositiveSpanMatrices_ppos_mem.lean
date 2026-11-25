-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices.ppos_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:59:35.290827+00:00
-- url     : https://prove2.me/submissions/ef7b28a8-1ffb-464f-9b39-3eae0d7912b6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveSpanMatrices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
theorem _root_.solution (x : Frame X.Ψ r) (τ : X.Ψ) (w : Fin r → ℂ) : X.ppos x τ w ∈ Spos X x τ := by
  unfold Data.ppos
  exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
end ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
