-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLatNm_exists_theta_eq_3f0873cb1a45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:51:37.794455+00:00
-- url     : https://prove2.me/submissions/65de8e63-a8b8-42ce-85fb-84f524590fc0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatNmSection

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.ChartLatNm
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
variable (P : ArithVariety n) (y : Coord n → Ω)
variable (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (hb : Geo.Birational (ι := blockIdx n) y)
namespace GroundTheory.Heights₂.Heights.ChartLatNm
theorem _root_.solution (c : (k : ι) → Fin (n k + 1)) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {u : P.FunField}
    (hu : u ∈ P.chartRing c) : ∃ x ∈ Geo.chartRingZ (ι := blockIdx n) y c, theta P y hP hb x = u := by
  have hle : P.chartRing c ≤ (Geo.chartRingZ (ι := blockIdx n) y c).toSubring.map (theta P y hP hb) := by
    refine Subring.closure_le.mpr ?_
    rintro _ ⟨p, rfl⟩
    exact Subring.mem_map.mpr ⟨_, Algebra.subset_adjoin ⟨p, rfl⟩, theta_chartCoord P y hP hb c hc p⟩
  obtain ⟨x, hx, hxu⟩ := Subring.mem_map.mp (hle hu)
  exact ⟨x, hx, hxu⟩
end GroundTheory.Heights₂.Heights.ChartLatNm
