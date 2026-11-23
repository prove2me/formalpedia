-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainTranslate.fd_translate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:52:50.580317+00:00
-- url     : https://prove2.me/submissions/da0afe26-a0fc-4e05-ad0f-58e6e4e7f0c8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainTranslate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainTranslate
open MeasureTheory Complex
open scoped Pointwise
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainTranslate
theorem _root_.solution (L : AddSubgroup (ι → ℝ)) [Countable L] (D : Set (ι → ℝ))
    (hD : IsAddFundamentalDomain L D volume) (f : (ι → ℝ) → ℂ) (hf : ∀ p ∈ L, ∀ s, f (p + s) = f s)
    (v : ι → ℝ) : ∫ s in D, f (v + s) = ∫ s in D, f s := by
  have hv : IsAddFundamentalDomain L (v +ᵥ D) volume := hD.vadd_of_comm v
  have h1 : ∫ s in D, f (v + s) = ∫ s in v +ᵥ D, f s := by
    have := (measurePreserving_add_left (volume : Measure (ι → ℝ)) v).setIntegral_image_emb
      (measurableEmbedding_addLeft v) f D
    rw [← this]
    rfl
  rw [h1]
  exact hv.setIntegral_eq hD (fun p s => hf p.1 p.2 s)
end ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainTranslate
