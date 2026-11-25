-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLatSection_coord_notMem_iff_c1ab93abd3c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:09:49.030615+00:00
-- url     : https://prove2.me/submissions/2cb39876-c9d2-48c9-a7a0-e7e767616ded

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatSection_form_mem_iff_6b464eb5ceeb

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
open GroundTheory.Heights₂.Heights.ChartLatSection
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.ChartLatSection
theorem _root_.solution (y : Coord n → Ω) {P : ArithVariety n}
    (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y) (p : Coord n) :
    (X p : MvPolynomial (Coord n) ℤ) ∉ P.ideal ↔ y p ≠ 0 := by
  rw [hP, form_mem_iff y (isWeightedHomogeneous_X ℤ (coordDeg n) p), aeval_X]
end GroundTheory.Heights₂.Heights.ChartLatSection
