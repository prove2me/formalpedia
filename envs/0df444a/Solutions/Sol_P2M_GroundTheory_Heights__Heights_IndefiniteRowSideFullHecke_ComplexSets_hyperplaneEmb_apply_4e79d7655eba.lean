-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hyperplaneEmb_apply_4e79d7655eba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:07:18.456161+00:00
-- url     : https://prove2.me/submissions/f39e2ab2-eccd-466c-bfe9-7ddfc1366cf5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceImmersiveGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalImageNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZeroSetOpenMass
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceImmersiveGeneral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology MeasureTheory
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (d : ℕ) (t : Fin d → ℂ) : hyperplaneEmb d t = Fin.cons 0 t := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [hyperplaneEmb]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
