-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_StokesOnVariety_hypotheses_inhabited_7c74f3903090
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:55:19.09784+00:00
-- url     : https://prove2.me/submissions/781f9d23-f910-4e6c-9272-531db3aa0f95

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isAffVariety_bot_ca242a8c4e80
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_contDiff_normSq_coord_a499efa3db51
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_smoothNear_of_contDiff_4853c0abca34
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_contDiff_lineBump_3fe718f1ee20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hasCompactSupport_lineBump_661426543a1f

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
open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff ENNReal
noncomputable section
variable {n d e : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace StokesOnVariety
theorem _root_.solution :
    IsAffVariety (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (0 + 1) ∧
      SmoothNear (zeroLocus (⊥ : Ideal (MvPolynomial (Fin 1) ℂ))) lineBump ∧
      SmoothNear (zeroLocus (⊥ : Ideal (MvPolynomial (Fin 1) ℂ))) (fun x => ‖x 0‖ ^ 2) ∧
      (HasCompactSupport lineBump ∨ HasCompactSupport (fun x : Fin 1 → ℂ => ‖x 0‖ ^ 2)) :=
  ⟨isAffVariety_bot 1, smoothNear_of_contDiff _ contDiff_lineBump,
    smoothNear_of_contDiff _ contDiff_normSq_coord, Or.inl hasCompactSupport_lineBump⟩
end StokesOnVariety
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
