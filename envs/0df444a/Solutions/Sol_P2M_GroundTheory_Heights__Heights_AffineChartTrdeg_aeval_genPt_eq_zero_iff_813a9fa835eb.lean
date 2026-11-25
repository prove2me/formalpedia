-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_aeval_genPt_eq_zero_iff_813a9fa835eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:31:16.636851+00:00
-- url     : https://prove2.me/submissions/cb334ddf-e444-4a94-a751-bcd398f46846

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsAlt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PAffineChartTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_aeval_genPt_179a6d344b31

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
open MvPolynomial
open GroundTheory.Heights₂.Heights.AffineChartTrdeg
variable {F : Type} [Field F] {n : ℕ} (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
omit [P.IsPrime]
namespace GroundTheory.Heights₂.Heights.AffineChartTrdeg
theorem _root_.solution (f : MvPolynomial (Fin n) F) :
    aeval (genPt P) f = 0 ↔ f ∈ P := by
  rw [aeval_genPt, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
end GroundTheory.Heights₂.Heights.AffineChartTrdeg
