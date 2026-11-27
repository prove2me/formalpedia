-- Prove2me | solution 1 for PositivityTheory.ThKF.L2.form_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:22:11.811653+00:00
-- url     : https://prove2.me/submissions/0ee842cb-0e36-441d-a77b-639169fe0e3b

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_IntegrableOnRight
import Theorems.Thm_PositivityTheory_ThKF_L2_integral_right

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
theorem _root_.solution (h : IsFundamentalDomain Γ 𝓕 μ) {f g : G → ℂ} (hf : Inv Γ f) (hg : Inv Γ g) (a : G) :
    ∫ x in 𝓕, conj (f (x * a)) * g (x * a) ∂μ = ∫ x in 𝓕, conj (f x) * g x ∂μ :=
  integral_right h (fun x => conj (f x) * g x) (fun γ hγ x => by rw [hf γ hγ, hg γ hγ]) a
end PositivityTheory.ThKF.L2
