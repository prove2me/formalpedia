-- Prove2me | solution 1 for PositivityTheory.ThKF.L2.integrableOn_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:31.544928+00:00
-- url     : https://prove2.me/submissions/8a848b7c-f7f9-48e8-bea4-4e80461b1a5c

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
theorem _root_.solution {E : Type} [NormedAddCommGroup E] (h : IsFundamentalDomain Γ 𝓕 μ) (F : G → E)
    (hF : ∀ γ ∈ Γ, ∀ x, F (γ * x) = F x) (hi : IntegrableOn F 𝓕 μ) (g : G) : IntegrableOn (fun x => F (x * g)) 𝓕 μ := by
  have h1 : IntegrableOn F ((fun x => x * g) '' 𝓕) μ :=
    ((fd_right h g).integrableOn_iff h fun γ x => hF γ γ.2 x).2 hi
  exact ((measurePreserving_mul_right μ g).integrableOn_image (emb g)).1 h1
end PositivityTheory.ThKF.L2
