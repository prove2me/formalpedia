-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.KU.rho_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:00:36.126857+00:00
-- url     : https://prove2.me/submissions/c4bee0c5-d98b-4e7e-b72e-4e84980c6474

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_Lemmata_GeneralBFactVariant_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_orth_dom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_lact_eq_of_rho
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_mul_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_oneF_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_rmul_oneF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_lact_lact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_lact_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.KU
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU
theorem _root_.solution (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) :
    Function.Injective ((rho X ho).comp X.Γ.subtype) := by
  intro γ γ' h
  have hl : lact γ.1 x0 = lact γ'.1 x0 := lact_eq_of_rho X ho h
  have hδ : (γ'.1)⁻¹ * γ.1 ∈ X.Γ := X.Γ.mul_mem (X.Γ.inv_mem γ'.2) γ.2
  have h1 : lact ((γ'.1)⁻¹ * γ.1) x0 = rmul x0 (ExtFPf.oneF X) := by
    rw [ExtFPf.rmul_oneF, ← lact_lact, hl, lact_lact, inv_mul_cancel, lact_one]
  have := X.Γ_free _ hδ x0 (orth_dom X ho) _ (ExtFPf.oneF_mem X) h1
  exact Subtype.ext (inv_mul_eq_one.mp this).symm
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU
