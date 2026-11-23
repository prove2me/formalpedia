-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.hermC_ppos_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:06.901408+00:00
-- url     : https://prove2.me/submissions/9ecf0d3f-fbbd-45e4-91fe-2e3aeb6ab7c1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Matrix NumberField
open scoped ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (τ : X.Ψ) (x : Frame X.Ψ r) (u : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ u) u = ∑ a, ∑ b, hermC τ.1 X.Gm u (X.colP x τ a) *
      (X.gramPos x τ)⁻¹ a b * conj (hermC τ.1 X.Gm u (X.colP x τ b)) := by
  rw [X.ppos_eq x τ u, hermC_sum_left]
  simp_rw [hermC_smul_left, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hermC_conj τ.1 X.Gm_herm u (X.colP x τ j)]
end ReciprocityTheory.ChartRestriction.G.FD.Data
