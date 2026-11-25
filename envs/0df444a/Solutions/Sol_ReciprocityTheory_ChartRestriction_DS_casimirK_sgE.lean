-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.casimirK_sgE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:51:11.751594+00:00
-- url     : https://prove2.me/submissions/512bac11-a015-45d3-bcda-8f7b65260582

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimirK_pm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_csq_sgE_mm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_csq_sgE_pp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sum_comm_pair_pair
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_two_rho_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
private theorem isCAR_cm_mul_cp_eq_delta_sub_cp_mul_cm {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (i a j b : Fin n) :
    cm i a * cp j b = (if i = j ∧ a = b then 1 else 0) - cp j b * cm i a :=
  eq_sub_of_add_eq (hC i a j b).2.2
private theorem isCAR_cm_mul_cm_eq_neg_swap {cp cm : Fin n → Fin n → Module.End ℂ W}
    (hC : IsCAR cp cm) (i a j b : Fin n) :
    cm i a * cm j b = -(cm j b * cm i a) :=
  eq_neg_of_add_eq_zero_left (hC i a j b).2.1
private theorem sum_sum_ite_eq_eq_sum {R ι : Type*} [AddCommMonoid R] [DecidableEq ι] (s : Finset ι)
    (f : ι → R) : ∑ x ∈ s, ∑ y ∈ s, (if x = y then f x else 0) = ∑ x ∈ s, f x :=
  Finset.sum_congr rfl fun x hx => by simp [hx]
private theorem isCAR_cp_cm_cp_cm_reorder_shared_snd {cp cm : Fin n → Fin n → Module.End ℂ W}
    (hC : IsCAR cp cm) (a b x y : Fin n) :
    cp a x * cm b x * (cp b y * cm a y) =
      (if x = y then cp a x * cm a x else 0) - cp a x * cp b y * (cm b x * cm a y) := by
  rw [show cp a x * cm b x * (cp b y * cm a y) = cp a x * (cm b x * cp b y) * cm a y by
    simp only [mul_assoc], isCAR_cm_mul_cp_eq_delta_sub_cp_mul_cm hC b x b y]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos ⟨rfl, rfl⟩, if_pos rfl]
    noncomm_ring
  · rw [if_neg (fun h => hxy h.2), if_neg hxy]
    noncomm_ring
private theorem isCAR_cp_cm_cp_cm_reorder_shared_fst {cp cm : Fin n → Fin n → Module.End ℂ W}
    (hC : IsCAR cp cm) (a b i j : Fin n) :
    cp i b * cm i a * (cp j a * cm j b) =
      (if i = j then cp i b * cm i b else 0) - cp i b * cp j a * (cm i a * cm j b) := by
  rw [show cp i b * cm i a * (cp j a * cm j b) = cp i b * (cm i a * cp j a) * cm j b by
    simp only [mul_assoc], isCAR_cm_mul_cp_eq_delta_sub_cp_mul_cm hC i a j a]
  by_cases hij : i = j
  · subst hij
    rw [if_pos ⟨rfl, rfl⟩, if_pos rfl]
    noncomm_ring
  · rw [if_neg (fun h => hij h.1), if_neg hij]
    noncomm_ring
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) (ε : Fin n → Bool) :
    casimirK ε (sgE ε cp cm) = (2 : ℂ) • ∑ a, ((rhoHol ε a : ℝ) : ℂ) • sgE ε cp cm a a := by
  have hpos : ∀ a ∈ plusIdx ε, ∀ b ∈ plusIdx ε,
      sgE ε cp cm a b * sgE ε cp cm b a =
        ∑ x ∈ minusIdx ε, ∑ y ∈ minusIdx ε,
          ((if x = y then cp a x * cm a x else 0) - cp a x * cp b y * (cm b x * cm a y)) := by
    intro a ha b hb
    rw [csq_sgE_pp ε cp cm ha hb, csq_sgE_pp ε cp cm hb ha, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => isCAR_cp_cm_cp_cm_reorder_shared_snd hC a b x y
  have hneg : ∀ a ∈ minusIdx ε, ∀ b ∈ minusIdx ε,
      sgE ε cp cm a b * sgE ε cp cm b a =
        ∑ i ∈ plusIdx ε, ∑ j ∈ plusIdx ε,
          ((if i = j then cp i b * cm i b else 0) - cp i b * cp j a * (cm i a * cm j b)) := by
    intro a ha b hb
    rw [csq_sgE_mm ε cp cm ha hb, csq_sgE_mm ε cp cm hb ha, neg_mul_neg,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => isCAR_cp_cm_cp_cm_reorder_shared_fst hC a b i j
  have hposBlock : ∑ a ∈ plusIdx ε, ∑ b ∈ plusIdx ε,
      sgE ε cp cm a b * sgE ε cp cm b a =
        (pOf ε : ℂ) •
            ∑ a ∈ plusIdx ε, ∑ x ∈ minusIdx ε, cp a x * cm a x -
          ∑ a ∈ plusIdx ε, ∑ b ∈ plusIdx ε, ∑ x ∈ minusIdx ε,
            ∑ y ∈ minusIdx ε, cp a x * cp b y * (cm b x * cm a y) := by
    rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hpos a ha b hb]
    simp only [Finset.sum_sub_distrib, sum_sum_ite_eq_eq_sum, Finset.sum_const, ← Finset.smul_sum]
    rw [Nat.cast_smul_eq_nsmul ℂ]
    rfl
  have hnegBlock : ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε,
      sgE ε cp cm a b * sgE ε cp cm b a =
        (qOf ε : ℂ) •
            ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε, cp i b * cm i b -
          ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε,
            ∑ j ∈ plusIdx ε, cp i b * cp j a * (cm i a * cm j b) := by
    rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hneg a ha b hb]
    simp only [Finset.sum_sub_distrib, sum_sum_ite_eq_eq_sum, Finset.sum_const]
    rw [Nat.cast_smul_eq_nsmul ℂ]
    rfl
  have hT : ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε,
        ∑ j ∈ plusIdx ε, cp i b * cp j a * (cm i a * cm j b) =
      -∑ a ∈ plusIdx ε, ∑ b ∈ plusIdx ε, ∑ x ∈ minusIdx ε,
        ∑ y ∈ minusIdx ε, cp a x * cp b y * (cm b x * cm a y) := by
    rw [sum_comm_pair_pair, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [isCAR_cm_mul_cm_eq_neg_swap hC i a j b, mul_neg]
  have hN : ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε, cp i b * cm i b =
      ∑ a ∈ plusIdx ε, ∑ x ∈ minusIdx ε, cp a x * cm a x := by
    rw [Finset.sum_comm]
  have hR1 : ∑ a ∈ plusIdx ε, (qOf ε : ℂ) • sgE ε cp cm a a =
      (qOf ε : ℂ) •
        ∑ a ∈ plusIdx ε, ∑ x ∈ minusIdx ε, cp a x * cm a x := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun a ha => by rw [csq_sgE_pp ε cp cm ha ha]
  have hR2 : ∑ a ∈ minusIdx ε, (pOf ε : ℂ) • sgE ε cp cm a a =
      -((pOf ε : ℂ) •
        ∑ b ∈ minusIdx ε, ∑ i ∈ plusIdx ε, cp i b * cm i b) := by
    rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a ha => by rw [csq_sgE_mm ε cp cm ha ha, smul_neg]
  rw [casimirK_pm, two_rho_sum, hposBlock,
    hnegBlock, hR1, hR2, hT, hN]
  abel
end ReciprocityTheory.ChartRestriction.DS
