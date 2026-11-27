-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BranchPlace_proof_12e09227e24f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:53:34.943796+00:00
-- url     : https://prove2.me/submissions/b7366ef7-9a04-4354-81b5-9997c171048c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchInComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMinimalPrimePlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeBranchPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchPlace

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
open MvPolynomial ComplexSets
namespace GroundTheory.Heights₂.Heights
namespace BranchPlace
theorem _root_.solution (h₁ : BranchInComponent.Statement) (h₂ : PrimeBranchPlace.Statement)
    (h₃ : MinimalPrimePlace.Statement) : BranchPlace.Statement := by
  intro n I q c hrad hdim
  obtain ⟨J, hJ, hmaps⟩ := h₁ n I 1 q c
  have hJp : J.IsPrime := hJ.1.1
  have hIJ : I ≤ J := hJ.1.2

  let c' : VarBranch J 1 q :=
    { radius := c.radius, radius_pos := c.radius_pos, toFun := c.toFun, differentiableOn := c.differentiableOn,
      injOn := c.injOn, map_zero := c.map_zero, mapsTo := hmaps }

  have hJq : J ≤ RingHom.ker (eval q) := by
    intro g hg
    have h0 := hmaps (Metric.mem_ball_self c.radius_pos) g hg
    rw [c.map_zero] at h0
    exact RingHom.mem_ker.2 h0

  have hdimJ : ringKrullDim (curveLocalRing J q) ≤ 1 := by
    have hle : I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) ≤
        J.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) :=
      Ideal.map_mono hIJ
    rw [← hdim]
    exact ringKrullDim_le_of_surjective
      (Ideal.Quotient.factor hle : curveLocalRing I q →+* curveLocalRing J q) (Ideal.Quotient.factor_surjective hle)
  obtain ⟨P', hP'⟩ := h₂ n J q c' hJp hdimJ
  obtain ⟨P, hP⟩ := h₃ n I J q hrad hJ hJq P'
  exact ⟨P, fun f ↦ (hP f).trans (hP' f)⟩
end BranchPlace
end GroundTheory.Heights₂.Heights
