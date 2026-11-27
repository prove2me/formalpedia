-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_comp_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:28:11.350562+00:00
-- url     : https://prove2.me/submissions/d7371c0b-369e-40b6-8637-d61ce4e6d417

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OpenRowsFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnChartX
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_ExpRowsPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_ExpRows_tangent_open_preimage_zero

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
theorem _root_.solution {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} (hol : IsHolFam e) (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ))
    {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Y} (hv : IsDerivAt0 e (D w) v) :
    IsDerivAt0 (fun z => e (D z)) w v := by
  refine ⟨by show _ = e (D 0); rw [map_zero]; exact hv.1, fun U h f => ?_⟩
  rw [hv.2 U h f]
  have h0 : (0 : Fin g → ℂ) ∈ {z | ⊤ ≤ e z ⁻¹ᵁ U} := tangent_open_preimage_zero hv U h
  have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) (D 0) := by
    rw [map_zero]
    exact ((hol U f).2 0 h0).differentiableAt ((hol U f).1.mem_nhds h0)
  have hc := fderiv_comp (0 : Fin g → ℂ) hd D.differentiableAt
  show _ = fderiv ℂ ((fun z => valAt' (e z) U f) ∘ D) 0 w
  rw [hc, ContinuousLinearMap.fderiv, map_zero]
  rfl
end ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows
