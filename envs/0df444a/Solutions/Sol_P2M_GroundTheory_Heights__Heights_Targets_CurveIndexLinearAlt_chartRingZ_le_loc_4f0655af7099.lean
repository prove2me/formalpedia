-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveIndexLinearAlt_chartRingZ_le_loc_4f0655af7099
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:21:11.624064+00:00
-- url     : https://prove2.me/submissions/80ac59d7-7486-4169-993a-cd9fed485e3d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveIndexLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveRingFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveIndexLinear

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveIndexLinearAlt
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets.CurveIndexLinearAlt
theorem _root_.solution {y : (Σ k, ι k) → Ω} {m : Ideal (curveRing y)} (hm : m.IsPrime) {c' : ∀ k, ι k}
    (hr : ∀ p : Σ k, ι k, ∃ α β : curveRing y, β ∉ m ∧ (β : Ω) * (y p / y ⟨p.1, c' p.1⟩) = α) {r : Ω}
    (hrc : r ∈ chartRingZ y c') : ∃ b : curveRing y, b ∉ m ∧ (b : Ω) * r ∈ curveRing y := by
  have hle : chartRingZ y c' ≤ subalgebraOfSubring (locRing m hm (curveRing y) fun b => b.2) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨p, rfl⟩
    obtain ⟨α, β, hβ, e⟩ := hr p
    exact mem_subalgebraOfSubring.mpr ⟨β, hβ, by rw [e]; exact α.2⟩
  exact mem_subalgebraOfSubring.mp (hle hrc)
end GroundTheory.Heights₂.Heights.Targets.CurveIndexLinearAlt
