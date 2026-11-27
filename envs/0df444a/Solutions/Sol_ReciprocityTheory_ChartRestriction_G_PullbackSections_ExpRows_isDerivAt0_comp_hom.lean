-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_comp_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:29:41.60686+00:00
-- url     : https://prove2.me/submissions/b1bf2de0-21ad-4bfd-9d85-daea7d68500a

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OpenRowsFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnChartX
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_ExpRowsPf
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__comp_88757af08841


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
theorem _root_.solution {Y' : Scheme.{0}} {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} {w : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ Y} (hv : IsDerivAt0 e w v) (φ : Y ⟶ Y') :
    IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ) := by
  refine ⟨by rw [← Category.assoc, hv.1], fun U h f => ?_⟩
  have h' : ⊤ ≤ v ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
  have key := hv.2 (φ ⁻¹ᵁ U) h' (φ.app U f)
  simp only [← valAt'_comp]
  rw [← key]
  have hc : (v ≫ φ).appLE U ⊤ h = φ.app U ≫ v.appLE (φ ⁻¹ᵁ U) ⊤ h' := by
    first
    | exact Scheme.comp_appLE v φ U ⊤ h
    | exact Scheme.Hom.comp_appLE v φ U ⊤ h
    | simp [Scheme.Hom.appLE]
  rw [hc]
  rfl
end ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows
