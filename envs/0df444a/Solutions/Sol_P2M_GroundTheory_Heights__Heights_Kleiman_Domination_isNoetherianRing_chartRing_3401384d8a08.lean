-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Domination_isNoetherianRing_chartRing_3401384d8a08
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:56:59.448817+00:00
-- url     : https://prove2.me/submissions/3ac8be51-688e-4bf3-8a4e-6d4ca89f29dd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_chartRing_eq_ampleBase_278a900ad2c3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.Domination
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.Domination
theorem _root_.solution [IsNoetherianRing S] {i : Fin (N + 1)} (hi : x i ≠ 0) :
    IsNoetherianRing (chartRing S x (singleChart hi)) := by
  classical
  have hfg : (chartRing S x (singleChart hi)).FG := by
    rw [chartRing_eq_ampleBase hi, ampleBase]
    refine ⟨Finset.univ.image fun l => x l / x i, ?_⟩
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have : Algebra.FiniteType S (chartRing S x (singleChart hi)) := ⟨(Subalgebra.fg_top _).mpr hfg⟩
  exact Algebra.FiniteType.isNoetherianRing S _
end GroundTheory.Heights₂.Heights.Kleiman.Domination
