-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_dOp__comm_diagE_7f96b23c099e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:29:58.506257+00:00
-- url     : https://prove2.me/submissions/ba4e6084-9e33-4b6d-93b5-799d5e5873a7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARKinv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_carKinv_sum_mul_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_carKinv_sg_cm_plus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_carKinv_sg_cm_minus
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_carKinv_term_d__e57617b1b86e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) (a b : Fin n) (hab : ε a = ε b) :
    dOp' ε E cm * diagE ε E cp cm a b = diagE ε E cp cm a b * dOp' ε E cm := by
  unfold dOp'
  rw [neg_mul, mul_neg, neg_inj]
  apply carKinv_sum_mul_comm
  simp_rw [carKinv_term_d' hE hEC]
  have hpl : ∀ x, x ∈ plusIdx ε ↔ ε x = true := fun x => by simp [plusIdx]
  have hmi : ∀ x, x ∈ minusIdx ε ↔ ε x = false := fun x => by simp [minusIdx]
  cases hεa : ε a
  ·
    have hεb : ε b = false := by rw [← hab]; exact hεa
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' := (hpl i).1 hi
    have hib : b ≠ i := by rintro rfl; simp_all
    rw [Finset.sum_congr rfl fun c _ => show
        ((if c = a then E i b else 0) - (if b = i then E a c else 0)) * cm i c -
          E i c * (sgE ε cp cm a b * cm i c - cm i c * sgE ε cp cm a b) =
        (if c = a then E i b * cm i a else 0) - (if c = b then E i b * cm i a else 0) by
      rw [carKinv_sg_cm_minus hC ε a b i c hεa hεb hi']
      split_ifs <;> subst_vars <;> (try simp_all) <;> (try noncomm_ring)]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos ((hmi a).2 hεa),
      if_pos ((hmi b).2 hεb), sub_self]
  ·
    have hεb : ε b = true := by rw [← hab]; exact hεa
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun c hc => ?_
    have hc' := (hmi c).1 hc
    have hca : c ≠ a := by rintro rfl; simp_all
    rw [Finset.sum_congr rfl fun i _ => show
        ((if c = a then E i b else 0) - (if b = i then E a c else 0)) * cm i c -
          E i c * (sgE ε cp cm a b * cm i c - cm i c * sgE ε cp cm a b) =
        (if i = a then E a c * cm b c else 0) - (if b = i then E a c * cm b c else 0) by
      rw [carKinv_sg_cm_plus hC ε a b i c hεa hεb hc']
      split_ifs <;> subst_vars <;> (try simp_all) <;> (try noncomm_ring)]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, if_pos ((hpl a).2 hεa),
      if_pos ((hpl b).2 hεb), sub_self]
end ReciprocityTheory.ChartRestriction.DS
