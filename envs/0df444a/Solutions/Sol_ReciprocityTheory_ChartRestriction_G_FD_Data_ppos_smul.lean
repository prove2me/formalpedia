-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.ppos_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:36.787946+00:00
-- url     : https://prove2.me/submissions/af7d3fa4-cce3-4802-9882-dc1077a5dc5a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowFixesComplementOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_smul_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.ppos x τ (c • v) = c • X.ppos x τ v := by
  simp only [ppos, hC_smul_left, Finset.smul_sum, smul_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  ring
end ReciprocityTheory.ChartRestriction.G.FD.Data
