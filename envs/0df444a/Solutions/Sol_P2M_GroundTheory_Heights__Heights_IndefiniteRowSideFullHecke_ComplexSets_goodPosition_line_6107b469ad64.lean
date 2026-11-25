-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_goodPosition_line_6107b469ad64
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:32:04.358948+00:00
-- url     : https://prove2.me/submissions/87c4d6fa-419a-48aa-8ce1-fc18bf18e29a

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_zeroLocus_bot_e7fa993f2e19
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eq_zero_of_mem_zeroLocus_lineOriginIdeal_2d18b27a0fed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_zero_mem_zeroLocus_lineOriginIdeal_10ee564c1f3c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_linVal_one_line_264d9e98ab6b

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
    GoodPosition (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) lineOriginIdeal (fun _ => 1) 0
      (0 : Matrix (Fin 0) (Fin 1) ℂ) (Metric.ball 0 1) Set.univ 1 1 where
  isOpen_U := Metric.isOpen_ball
  isBounded_U := Metric.isBounded_ball
  mem_U := Metric.mem_ball_self one_pos
  mem_W := zero_mem_zeroLocus_lineOriginIdeal
  isOpen_V := isOpen_univ
  mem_V := Set.mem_univ _
  pos := one_pos
  zeros q _ _ hq _ := by
    rw [linVal_one_line] at hq
    have hq0 : q = 0 := by
      funext i
      rw [Fin.fin_one_eq_zero i]
      exact hq
    subst hq0
    exact ⟨Metric.mem_ball_self one_pos, zero_mem_zeroLocus_lineOriginIdeal⟩
  injOn q hq q' hq' _ := by
    rw [eq_zero_of_mem_zeroLocus_lineOriginIdeal hq.2, eq_zero_of_mem_zeroLocus_lineOriginIdeal hq'.2]
  count w _ t _ ht := by
    have hset : {x | x ∈ Metric.ball (0 : Fin 1 → ℂ) 1 ∩ zeroLocus (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
        (0 : Matrix (Fin 0) (Fin 1) ℂ) *ᵥ x = w ∧ linVal (fun _ => (1 : ℂ)) x = t} =
        {fun _ => t} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_inter_iff, linVal_one_line]
      constructor
      · rintro ⟨-, -, hx⟩
        funext i
        rw [Fin.fin_one_eq_zero i]
        exact hx
      · rintro rfl
        refine ⟨⟨?_, mem_zeroLocus_bot _⟩, Subsingleton.elim _ _, rfl⟩
        rw [Metric.mem_ball, dist_zero_right, pi_norm_const]
        exact ht
    rw [hset, Set.encard_singleton]
    rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
