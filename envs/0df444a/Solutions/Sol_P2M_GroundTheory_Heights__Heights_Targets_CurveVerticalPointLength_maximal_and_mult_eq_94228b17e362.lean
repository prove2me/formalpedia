-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointLength_maximal_and_mult_eq_94228b17e362
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:25:53.608691+00:00
-- url     : https://prove2.me/submissions/c654d1c0-d8ec-46f1-8ad7-2060b735a05d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertPointLengthSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CurveCountObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MultAtPosOfMemDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveVertPointLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ne_zero_of_X_notMem_641fc42e6473


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointLength
namespace GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointLength
theorem _root_.solution (hCh : CurveVertPointChart.Statement) (hMC : CurveVertPointMultChart.Statement)
    (hSQ : CurveSectionQuotLocal.Statement) {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {s : MRing ι} {d : K → ℕ}
    (hP : IsArithVar (mCoordIdeal y) 1) (hs : IsMultiHomog s d) (hsP : s ∉ mCoordIdeal y)
    {W : Ideal (MRing ι)} (hW : W ∈ divSupp (mCoordIdeal y) s) :
    (curvePtIdeal y W).IsMaximal ∧
      multAt (mCoordIdeal y ⊔ Ideal.span {s}) W =
        locLen (curvePtIdeal y W) (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) := by
  choose c hc using hW.2
  obtain ⟨hmax, hrat, hmem⟩ := hCh K ι Ω y s d hP hs hsP W hW c hc
  have hPW : mCoordIdeal y ≤ W := le_trans le_sup_left hW.1.1.2
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => ne_zero_of_X_notMem fun h => hc k (hPW h)
  obtain ⟨a, b, -, hb, hab⟩ := (hmem d s hs).mp hsW
  refine ⟨hmax, ?_⟩
  rw [hMC K ι Ω y s d hP hs hsP W hW c hc a b hb hab,
    hSQ K ι Ω y s d hP hs hsP _ c hmax.isPrime hyc hrat a b hb hab]
end GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointLength
