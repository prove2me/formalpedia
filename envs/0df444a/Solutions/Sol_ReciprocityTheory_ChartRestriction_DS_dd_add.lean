-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.dd_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:45.998823+00:00
-- url     : https://prove2.me/submissions/8dda6f20-06a6-4145-bee1-50f1bfe0d2e9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_csq_dd_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_csq_sgE_mm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_csq_sgE_pp


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
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) :
    dOp ε E cp * dOp' ε E cm + dOp' ε E cm * dOp ε E cp =
      -(∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, E i a * E a i) + crossT ε E cp cm := by
  have e1 : dOp ε E cp * dOp' ε E cm =
      -∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
        E a i * cp i a * (E j b * cm j b) := by
    unfold dOp dOp'
    rw [mul_neg, Finset.sum_mul_sum, neg_inj]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_mul_sum]
    exact Finset.sum_comm
  have e2 : dOp' ε E cm * dOp ε E cp =
      -∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
        E j b * cm j b * (E a i * cp i a) := by
    unfold dOp dOp'
    rw [neg_mul, Finset.sum_mul_sum, neg_inj]
    simp only [Finset.sum_mul_sum]
    calc ∑ j ∈ plusIdx ε, ∑ i ∈ plusIdx ε, ∑ b ∈ minusIdx ε, ∑ a ∈ minusIdx ε,
          E j b * cm j b * (E a i * cp i a)
        = ∑ i ∈ plusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε, ∑ a ∈ minusIdx ε,
          E j b * cm j b * (E a i * cp i a) := Finset.sum_comm
      _ = ∑ i ∈ plusIdx ε, ∑ j ∈ plusIdx ε, ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε,
          E j b * cm j b * (E a i * cp i a) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_comm
  have hX : dOp ε E cp * dOp' ε E cm + dOp' ε E cm * dOp ε E cp =
      -(∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
        (E a i * cp i a * (E j b * cm j b) + E j b * cm j b * (E a i * cp i a))) := by
    rw [e1, e2]
    simp only [Finset.sum_add_distrib]
    abel
  have hA : ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
      (if i = j then E a b * (cp i a * cm j b) else 0) =
      ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε, E a b * (cp i a * cm i b) := by
    have h1 : ∀ i ∈ plusIdx ε, ∀ a, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
        (if i = j then E a b * (cp i a * cm j b) else 0) =
        ∑ b ∈ minusIdx ε, E a b * (cp i a * cm i b) := by
      intro i hi a
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_ite_eq, if_pos hi]
    refine (Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun a _ => h1 i hi a).trans ?_
    exact Finset.sum_comm.trans (Finset.sum_congr rfl fun a _ => Finset.sum_comm)
  have hB : ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
      (if b = a then E j i * (cp i a * cm j b) else 0) =
      ∑ x ∈ plusIdx ε, ∑ y ∈ plusIdx ε, ∑ c ∈ minusIdx ε, E x y * (cp y c * cm x c) := by
    have h1 : ∀ i, ∀ a ∈ minusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
        (if b = a then E j i * (cp i a * cm j b) else 0) =
        ∑ j ∈ plusIdx ε, E j i * (cp i a * cm j a) := by
      intro i a ha
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_ite_eq', if_pos ha]
    refine (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a ha => h1 i a ha).trans ?_
    exact (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm
  have hC' : ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, ∑ j ∈ plusIdx ε, ∑ b ∈ minusIdx ε,
      (if b = a then (if j = i then E i a * E a i else 0) else 0) =
      ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, E i a * E a i := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_congr rfl fun j _ => (by rw [Finset.sum_ite_eq', if_pos ha] :
      ∑ b ∈ minusIdx ε, (if b = a then (if j = i then E i a * E a i else 0) else 0) =
        (if j = i then E i a * E a i else 0))]
    rw [Finset.sum_ite_eq', if_pos hi]
  have hcross : crossT ε E cp cm =
      ∑ x ∈ plusIdx ε, ∑ y ∈ plusIdx ε, ∑ c ∈ minusIdx ε, E x y * (cp y c * cm x c) -
        ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε, E a b * (cp i a * cm i b) := by
    unfold crossT
    rw [sub_eq_add_neg]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
      rw [csq_sgE_pp ε cp cm hy hx, Finset.mul_sum]
    · rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [csq_sgE_mm ε cp cm hb ha, mul_neg, Finset.mul_sum]
  rw [hX]
  simp only [csq_dd_pt hE hC hEC, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hA, hB, hC', hcross]
  abel
end ReciprocityTheory.ChartRestriction.DS
