-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BranchNormalisation_proof_8cd54afc0fc1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:53:32.309212+00:00
-- url     : https://prove2.me/submissions/b1548ffe-b1c5-4d61-aa10-2262c86df4e2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchNormalisation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchGermDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSameOrderBranchesMeet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPlaceHasBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOrdDeterminesPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveResidueDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOrdFiniteNonZeroDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchNormalisation

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
open MvPolynomial ComplexSets Filter Topology
namespace GroundTheory.Heights₂.Heights
namespace BranchNormalisation
theorem _root_.solution (h₀ : BranchGermDimOne.Statement) (h₁ : BranchPlace.Statement)
    (h₂ : SameOrderBranchesMeet.Statement) (h₃ : PlaceHasBranch.Statement)
    (h₄ : OrdDeterminesPlace.Statement) (h₅ : CurveResidueDegree.Statement)
    (h₆ : OrdFiniteNonZeroDivisor.Statement) : BranchNormalisation.Statement := by
  intro n I q m c hrad hm hcov hdisj
  have hdim := h₀ n I q m c hm hcov
  refine ⟨hdim, fun f hf ↦ h₆ n I q f hrad hdim fun P ↦ ?_, ?_⟩
  · obtain ⟨b, hb⟩ := h₃ n I q m c hrad hdim hcov hdisj P
    rw [hb f]
    exact hf b
  choose P hP using fun b ↦ h₁ n I q (c b) hrad hdim

  have hcongr : ∀ Q Q' : MaximalSpectrum (curveNormalisation I q), Q = Q' → ∀ f : MvPolynomial (Fin n) ℂ,
      Ring.ord (Localization.AtPrime Q.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime Q.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) =
      Ring.ord (Localization.AtPrime Q'.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime Q'.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) := by
    rintro Q _ rfl f
    rfl
  have hinj : Function.Injective P := by
    intro b b' hbb
    by_contra hne
    obtain ⟨x, hx, hxq⟩ := h₂ n I q (c b) (c b') hrad hdim fun f ↦
      (hP b f).symm.trans ((hcongr _ _ hbb f).trans (hP b' f))
    exact hxq (hdisj b b' hne hx)
  have hsurj : Function.Surjective P := by
    intro Q
    obtain ⟨b, hb⟩ := h₃ n I q m c hrad hdim hcov hdisj Q
    exact ⟨b, h₄ n I q hrad hdim (P b) Q fun f ↦ (hP b f).trans (hb f).symm⟩
  exact ⟨Equiv.ofBijective P ⟨hinj, hsurj⟩, fun b ↦ ⟨h₅ n I q hrad hdim (P b), hP b⟩⟩
end BranchNormalisation
end GroundTheory.Heights₂.Heights
