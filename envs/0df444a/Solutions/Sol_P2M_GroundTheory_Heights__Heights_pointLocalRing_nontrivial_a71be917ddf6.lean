-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_pointLocalRing_nontrivial_a71be917ddf6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:36:11.650722+00:00
-- url     : https://prove2.me/submissions/489e9d7b-c05a-4a88-9a28-fd1db7317167

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
    (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I) : Nontrivial (pointLocalRing I w) := by
  unfold pointLocalRing
  rw [Ideal.Quotient.nontrivial_iff]
  intro htop
  have hle : I.map (algebraMap (MvPolynomial σ ℂ)
      (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)))) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))) := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ g).2 (RingHom.mem_ker.2 (hw g hg))
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 (htop ▸ hle))
end GroundTheory.Heights₂.Heights
