-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_pointLocalRing_subsingleton_b598c07e40ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:11:29.897118+00:00
-- url     : https://prove2.me/submissions/dc62c98b-8ee9-4c2a-b01b-aed6735ef5fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {σ : Type*}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ)
    (hw : w ∉ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I) : Subsingleton (pointLocalRing I w) := by
  simp only [IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn, Set.mem_ofPred_eq, not_forall] at hw
  obtain ⟨g, hg, hgw⟩ := hw
  unfold pointLocalRing
  rw [Ideal.Quotient.subsingleton_iff]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hg)
    (IsLocalization.map_units _
      (⟨g, fun h ↦ hgw (RingHom.mem_ker.1 h)⟩ : (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)).primeCompl))
end GroundTheory.Heights₂.Heights
