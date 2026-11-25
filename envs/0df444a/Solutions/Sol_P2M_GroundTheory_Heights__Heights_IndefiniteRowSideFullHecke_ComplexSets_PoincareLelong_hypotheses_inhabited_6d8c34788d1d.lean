-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PoincareLelong_hypotheses_inhabited_6d8c34788d1d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:55:13.668315+00:00
-- url     : https://prove2.me/submissions/d4789da1-5390-45ee-8c94-2f5aa544fa31

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isAffVariety_bot_ca242a8c4e80
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_contDiff_lineBump_3fe718f1ee20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hasCompactSupport_lineBump_661426543a1f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_one_not_mem_point_805b757dbb4c


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
namespace PoincareLelong
theorem _root_.solution :
    IsAffVariety (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (0 + 1) ∧
      linForm (fun _ : Fin 1 => (1 : ℂ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
      ContDiff ℝ ∞ lineBump ∧ HasCompactSupport lineBump :=
  ⟨isAffVariety_bot 1, linForm_one_not_mem_point ℂ, contDiff_lineBump, hasCompactSupport_lineBump⟩
end PoincareLelong
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
