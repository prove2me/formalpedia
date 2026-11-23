-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.Hf_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:08.439201+00:00
-- url     : https://prove2.me/submissions/2c93a5ff-bcf3-4b71-92c5-a2bfa7be639f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowFixesComplementOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_selfadj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_sub_left


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
theorem _root_.solution (x : Frame X.Ψ r) (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    X.Hf x τ u w = hermC τ.1 X.Gm u ((2 : ℂ) • X.ppos x τ w - w) := by
  have hneg : hermC τ.1 X.Gm u (-w) = - hermC τ.1 X.Gm u w := by
    have := hC_smul_right τ.1 X.Gm (-1) u w
    simpa using this
  calc X.Hf x τ u w = 2 * hermC τ.1 X.Gm u (X.ppos x τ w) - hermC τ.1 X.Gm u w := by
        simp only [Hf]; rw [hC_sub_left, hC_smul_left, ppos_selfadj X hx]
    _ = hermC τ.1 X.Gm u ((2 : ℂ) • X.ppos x τ w - w) := by
        rw [sub_eq_add_neg ((2 : ℂ) • X.ppos x τ w) w, hC_add_right, hC_smul_right, hneg, map_ofNat]
        ring
end ReciprocityTheory.ChartRestriction.G.FD.Data
