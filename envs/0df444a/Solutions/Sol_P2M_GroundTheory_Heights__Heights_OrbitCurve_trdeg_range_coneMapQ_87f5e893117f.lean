-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitCurve_trdeg_range_coneMapQ_87f5e893117f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:48.963506+00:00
-- url     : https://prove2.me/submissions/081bb5f8-e592-414d-9ee0-ca531eedb9b2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCurve
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_algebraicIndependent_C_mul_X_46ec521998de
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_exists_chart_5599c818fd08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_chart_3cad6f9af78e


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G Algebra
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitCurve
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.OrbitCurve
theorem _root_.solution {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) :
    trdeg ℚ (coneMapQ x).range = Fintype.card ι := by
  obtain ⟨c, hc⟩ := exists_chart hx
  refine le_antisymm ?_ ?_
  · calc trdeg ℚ (coneMapQ x).range ≤ trdeg ℚ (MvPolynomial ι (AlgebraicClosure ℚ)) :=
          trdeg_le_of_injective (coneMapQ x).range.val Subtype.val_injective
      _ = Fintype.card ι := by
          have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
          rw [← trdeg_add_eq ℚ (AlgebraicClosure ℚ) (A := MvPolynomial ι (AlgebraicClosure ℚ)),
            trdeg_eq_zero, MvPolynomial.trdeg_of_isDomain]
          simp
  · let u : ι → (coneMapQ x).range := fun k ↦
      ⟨C (x k (c k)) * X k, ⟨X ⟨k, c k⟩, by simp [coneMapQ, flatCone]⟩⟩
    have hu : AlgebraicIndependent ℚ u :=
      AlgebraicIndependent.of_comp (coneMapQ x).range.val (algebraicIndependent_C_mul_X _ hc)
    simpa using hu.cardinalMk_le_trdeg
end GroundTheory.Heights₂.Heights.OrbitCurve
