-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.ev_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:31:21.347365+00:00
-- url     : https://prove2.me/submissions/238df9ed-9cb6-4938-9126-1cfa153573a2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamCore
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_IdemDataBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamData
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_sum_omDF_omF

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
open NumberField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
theorem _root_.solution {k : Type} [Field k] (ψ : E →+* k) (δ : 𝓞 E) (hδ : ∀ i, IsIntegral ℤ ((δ : E) * omDF (E := E) i))
    (hψδ : ψ (δ : E) ≠ 0) : evD (ψ.comp (algebraMap (𝓞 E) E)) (bD δ hδ) (cD ψ δ) = 1 := by
  unfold evD cD bD
  have e : ∀ i, ψ (omF (E := E) i : E) / ψ (δ : E) *
      (ψ.comp (algebraMap (𝓞 E) E)) ⟨(δ : E) * omDF i, hδ i⟩ = ψ (omDF i * omF i) := by
    intro i
    show ψ (omF (E := E) i : E) / ψ (δ : E) * ψ ((δ : E) * omDF i) = _
    rw [map_mul, map_mul]
    field_simp
  rw [Finset.sum_congr rfl fun i _ => e i, ← map_sum, sum_omDF_omF, map_one]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
