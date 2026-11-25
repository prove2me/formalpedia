-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_LocalOrder_hypotheses_inhabited_78399301e491
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:01:22.433583+00:00
-- url     : https://prove2.me/submissions/9be078f3-68b0-428e-9bc0-60c7865d0567

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isAffVariety_bot_ca242a8c4e80
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_lineOriginIdeal_mem_minimalPrimes_b3cbcbf2f3e2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_goodPosition_line_6107b469ad64
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
namespace LocalOrder
theorem _root_.solution :
    IsAffVariety (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (0 + 1) ∧
      linForm (fun _ : Fin 1 => (1 : ℂ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
      lineOriginIdeal ∈ ((⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ⊔
        Ideal.span {linForm (fun _ : Fin 1 => (1 : ℂ))}).minimalPrimes ∧
      GoodPosition (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) lineOriginIdeal (fun _ => 1) 0
        (0 : Matrix (Fin 0) (Fin 1) ℂ) (Metric.ball 0 1) Set.univ 1 1 :=
  ⟨isAffVariety_bot 1, linForm_one_not_mem_point ℂ, lineOriginIdeal_mem_minimalPrimes, goodPosition_line⟩
end LocalOrder
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
