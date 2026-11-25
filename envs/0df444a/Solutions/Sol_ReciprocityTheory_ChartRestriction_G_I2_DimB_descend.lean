-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimB.descend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:14:33.101815+00:00
-- url     : https://prove2.me/submissions/15806a03-b5ad-4179-9eae-5680aae95cdf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_tproj_oqm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_tproj_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Complex
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.DimB
variable {k : ℕ}
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_11
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_13
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_16
namespace ReciprocityTheory.ChartRestriction.G.I2.DimB
theorem _root_.solution (φ : (Fin k → ℝ) → ℂ) (hφ : Continuous φ)
    (hp : ∀ (n : Fin k → ℤ) t, φ (t + fun i => (n i : ℝ)) = φ t) :
    ∃ D : C(UnitAddTorus (Fin k), ℂ), ∀ t, D (tproj t) = φ t := by
  let D0 : UnitAddTorus (Fin k) → ℂ := fun θ => φ (Function.surjInv tproj_oqm.surjective θ)
  have hD : ∀ t, D0 (tproj t) = φ t := by
    intro t
    obtain ⟨n, hn⟩ := tproj_eq (Function.surjInv_eq tproj_oqm.surjective (tproj t))
    have e := hp n (Function.surjInv tproj_oqm.surjective (tproj t))
    rw [← hn] at e
    exact e.symm
  refine ⟨⟨D0, ?_⟩, hD⟩
  rw [tproj_oqm.isQuotientMap.continuous_iff]
  have : D0 ∘ tproj = φ := funext hD
  rw [this]; exact hφ
end ReciprocityTheory.ChartRestriction.G.I2.DimB
