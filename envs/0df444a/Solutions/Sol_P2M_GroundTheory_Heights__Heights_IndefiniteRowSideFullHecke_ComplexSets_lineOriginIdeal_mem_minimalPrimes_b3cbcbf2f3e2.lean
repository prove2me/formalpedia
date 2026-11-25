-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_lineOriginIdeal_mem_minimalPrimes_b3cbcbf2f3e2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:32:46.377819+00:00
-- url     : https://prove2.me/submissions/849b3f9d-07fb-4214-a37c-bf090b96fbd8

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_linForm_one_line_a24be3fc1761
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_lineOriginIdeal_le_111e6fb81d81
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_X_mem_lineOriginIdeal_62be9b559b35

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
theorem _root_.solution :
    lineOriginIdeal ∈ ((⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ⊔
      Ideal.span {linForm (fun _ : Fin 1 => (1 : ℂ))}).minimalPrimes := by
  rw [linForm_one_line, bot_sup_eq]
  refine ⟨⟨RingHom.ker_isPrime _, ?_⟩, ?_⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact X_mem_lineOriginIdeal
  · intro P hP _
    exact lineOriginIdeal_le.trans hP.2
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
