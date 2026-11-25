-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary.sum_mem_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:54:17.504197+00:00
-- url     : https://prove2.me/submissions/b140b790-eec9-494c-bdf4-fea3fe4b8e2d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpSpanRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
  (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
namespace ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
theorem _root_.solution {n : ℕ} (Y : Fin n → Fin r → ℂ) (S : Set (Fin n)) (w : Fin n → ℂ)
    (hw : ∀ j, j ∉ S → w j = 0) : ∑ j, w j • Y j ∈ Submodule.span ℂ (Y '' S) := by
  refine Submodule.sum_mem _ (fun j _ => ?_)
  by_cases hj : j ∈ S
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · rw [hw j hj, zero_smul]
    exact Submodule.zero_mem _
end ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
