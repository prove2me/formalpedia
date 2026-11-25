-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_map_eq_zero_iff_8a5dd37f9c47
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:56:11.038466+00:00
-- url     : https://prove2.me/submissions/db133a90-8561-414a-a64b-4c7d5152fee9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartTrdeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.MChartTrdeg
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
variable (P : Ideal (MRing ι F)) [P.IsPrime]
omit [Fintype K] [DecidableEq K] [P.IsPrime]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.MChartTrdeg
theorem _root_.solution (f : MRing ι F) :
    algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) = 0 ↔ f ∈ P := by
  rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
end GroundTheory.Heights₂.Heights.FieldNumbers.MChartTrdeg
