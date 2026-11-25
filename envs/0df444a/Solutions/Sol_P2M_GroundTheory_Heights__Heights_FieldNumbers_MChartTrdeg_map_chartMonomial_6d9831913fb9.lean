-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_map_chartMonomial_6d9831913fb9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:12:28.676865+00:00
-- url     : https://prove2.me/submissions/a361cb4b-c68b-4539-b2dd-c65dadcfba1b

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
omit [DecidableEq K] [P.IsPrime]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.MChartTrdeg
theorem _root_.solution (u : ∀ k, ι k) (b : K → ℕ) :
    algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (chartMonomial u b)) =
      ∏ k, algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
        (Ideal.Quotient.mk P (X ⟨k, u k⟩)) ^ b k := by
  simp [chartMonomial, map_prod, map_pow]
end GroundTheory.Heights₂.Heights.FieldNumbers.MChartTrdeg
