-- Prove2me | solution 1 for PositivityTheory.HtPt.KtwS.StepTwo.proof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:04:08.995749+00:00
-- url     : https://prove2.me/submissions/0e09fa2a-3c20-45e0-a472-1f60c6758d3a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_Development_WeilBound_CoreStatements_HodgeTatePoints_ExistsLineBundleTwistMulOf
import Theorems.Thm_PositivityTheory_HtPt_KtwS_exists_lineBundle_pow
import Theorems.Thm_PositivityTheory_HtPt_KtwS_exists_lineBundle_twistMulOf
import Theorems.Thm_PositivityTheory_HtPt_KtwS_StepTwo_onW

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.HtPt PositivityTheory.HtPt.KtwS
open GroundTheory.Heights₂.Heights.Kleiman MvPolynomial
noncomputable section
universe u v w
namespace PositivityTheory.HtPt.KtwS
namespace StepTwo
theorem _root_.solution (hRed : StepTwo.Reduce.Statement.{u, v, w}) (hLT : LineTwist.Statement.{u, w})
    (hTA : TwistAlg.Statement.{u, w}) (hRT : RestrictTwist.Statement.{u, w})
    (hNR : NefRestrict.Statement.{u, w}) (hJP : StepData.JProper.Statement.{u, w})
    (hDrop : SubvarDrop.Statement.{u, w}) (hPt : PrimeFiltration.Point.Statement.{u, w})
    (hRes : PrimeFiltration.Restrict.Statement.{u, w})
    (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w}) (hTV : TwistVanish.Statement.{u, w}) :
    StepTwo.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x T hK E _ _ _ _ M₁ M₂ hle hJ
  obtain ⟨n, pr, sh, hpr, hred⟩ := hRed k Ω N x E M₁ M₂ hle T.J hJ
  have hLpow : ∀ b : ℕ, ∃ Q : LineBundle k x, Q.toSubSystem = T.L.pow b := fun b => by
    obtain ⟨L, hL⟩ := exists_lineBundle_twistMulOf hLT T.M T.p T.m
    obtain ⟨Q, hQ⟩ := exists_lineBundle_pow hLT L b
    exact ⟨Q, by rw [hQ, hL]; rfl⟩
  choose Qb hQb using hLpow
  have hW : ∀ i, ∃ c₁ : ℤ, (∃ j, (X j : Poly k N) ∉ pr i) → ∀ (b : ℕ) (c : ℤ), c₁ ≤ c →
      Subsingleton (SubSystem.quotH ((Qb b).twist (twistSys k x c))
        (((Qb b).twist (twistSys k x c)).twist (idealSys x (pr i))) 1) := by
    intro i
    by_cases hrel : ∃ j, (X j : Poly k N) ∉ pr i
    · obtain ⟨c₁, hc₁⟩ := StepTwo.onW hLT hTA hRT hNR hJP hDrop hPt hRes hRQ hTV T hK (pr i)
        (hpr i).1 (hpr i).2.1 (hpr i).2.2.1 (hpr i).2.2.2 hrel
      exact ⟨c₁, fun _ b c hc => hc₁ b (Qb b) (hQb b) c hc⟩
    · exact ⟨0, fun h => absurd h hrel⟩
  choose cw hcw using hW
  refine ⟨∑ i, |cw i - sh i|, fun b c hc => ?_⟩
  have hs := hred (Qb b) c (fun i hi => hcw i hi b (c + sh i) (by
    have h1 : |cw i - sh i| ≤ ∑ i, |cw i - sh i| :=
      Finset.single_le_sum (f := fun i => |cw i - sh i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := le_abs_self (cw i - sh i)
    linarith))
  rwa [hQb b] at hs
end StepTwo
end PositivityTheory.HtPt.KtwS
