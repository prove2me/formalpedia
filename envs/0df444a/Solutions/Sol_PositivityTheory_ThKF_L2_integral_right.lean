-- Prove2me | solution 1 for PositivityTheory.ThKF.L2.integral_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:41.87228+00:00
-- url     : https://prove2.me/submissions/5c7284fb-753a-44de-957d-0e38ad59287a

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_IntegrableOnRight
import Theorems.Thm_PositivityTheory_ThKF_L2_fd_right
import Theorems.Thm_PositivityTheory_ThKF_L2_emb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF PositivityTheory.ThKF.L2
open MeasureTheory
open scoped ComplexConjugate Pointwise
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable Γ] {𝓕 : Set G}
namespace PositivityTheory.ThKF.L2
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : IsFundamentalDomain Γ 𝓕 μ) (F : G → E)
    (hF : ∀ γ ∈ Γ, ∀ x, F (γ * x) = F x) (g : G) : ∫ x in 𝓕, F (x * g) ∂μ = ∫ x in 𝓕, F x ∂μ := by
  rw [← (measurePreserving_mul_right μ g).setIntegral_image_emb (emb g) F 𝓕]
  exact (fd_right h g).setIntegral_eq h fun γ x => hF γ γ.2 x
end PositivityTheory.ThKF.L2
