-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.tangent_open_preimage_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:16:54.798523+00:00
-- url     : https://prove2.me/submissions/d93ae220-adbf-4db3-be10-37964f2b3c04

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OpenRowsFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnChartX
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_ExpRowsPf

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows
open AlgebraicGeometry CategoryTheory Opposite NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped MonObj
variable {g : ℕ} {Y : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows
theorem _root_.solution {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Y}
    (hv : IsDerivAt0 e w v) (U : Y.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) : ⊤ ≤ (e 0) ⁻¹ᵁ U := by
  intro x _
  rw [← hv.1]
  have hx := h (show (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
  first
  | exact hx
  | (simp only [Scheme.Hom.mem_preimage, Scheme.comp_base_apply] at hx ⊢; exact hx)
end ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows
