-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.sg_cp_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:24:02.010029+00:00
-- url     : https://prove2.me/submissions/901794b6-a815-405e-b7cf-3474aa5e77de

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
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
variable {n : ℕ}
section Comm
variable {W : Type*} [AddCommGroup W] [Module ℂ W]
private theorem car_mul_mul_commute_add_ite {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (a b y i x : Fin n) :
    cp a y * cm b y * cp i x =
      cp i x * (cp a y * cm b y) + (if b = i ∧ y = x then cp a y else 0) := by
  have e1 : cp a y * cp i x = -(cp i x * cp a y) := eq_neg_of_add_eq_zero_left (hC a y i x).1
  have e3 : cm b y * cp i x = (if b = i ∧ y = x then 1 else 0) - cp i x * cm b y :=
    eq_sub_of_add_eq (hC b y i x).2.2
  rw [mul_assoc, e3, mul_sub, ← mul_assoc (cp a y) (cp i x), e1]
  split_ifs <;> simp [mul_assoc, add_comm]
end Comm
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm) (ε : Fin n → Bool)
    (c i x : Fin n) :
    sgE ε cp cm c c * cp i x = cp i x * sgE ε cp cm c c + ((modeWt ε (i, x) c : ℝ) : ℂ) • cp i x := by
  unfold sgE
  by_cases hc : ε c = true
  · rw [if_pos ⟨hc, hc⟩, Finset.sum_mul, Finset.mul_sum]
    simp_rw [car_mul_mul_commute_add_ite hC]
    rw [Finset.sum_add_distrib]
    congr 1
    by_cases hci : c = i
    · subst hci
      simp only [true_and]
      rw [Finset.sum_ite_eq']
      by_cases hx : ε x = false
      · have hxc : x ≠ c := fun h => by rw [h, hc] at hx; exact Bool.noConfusion hx
        simp [minusIdx, hx, hc, modeWt, root, Pi.single_apply, hxc]
      · simp [minusIdx, hx, modeWt]
    · simp only [hci, false_and, if_false, Finset.sum_const_zero]
      by_cases hx : ε i = true ∧ ε x = false
      · have hxc : x ≠ c := fun h => by rw [h, hc] at hx; exact Bool.noConfusion hx.2
        simp [modeWt, hx, root, Pi.single_apply, Ne.symm hci, hxc]
      · simp [modeWt, hx]
  · have hc' : ε c = false := by simpa using hc
    rw [if_neg (fun h => hc h.1), if_pos ⟨hc', hc'⟩, neg_mul, mul_neg, Finset.sum_mul, Finset.mul_sum]
    simp_rw [car_mul_mul_commute_add_ite hC]
    rw [Finset.sum_add_distrib, neg_add]
    congr 1
    by_cases hcx : c = x
    · subst hcx
      simp only [eq_self_iff_true, and_true]
      rw [Finset.sum_ite_eq']
      by_cases hi : ε i = true
      · have hic : i ≠ c := fun h => by rw [h, hc'] at hi; exact Bool.noConfusion hi
        simp [plusIdx, hi, hc', modeWt, root, Pi.single_apply, hic]
      · simp [plusIdx, hi, modeWt]
    · simp only [hcx, and_false, if_false, neg_zero, Finset.sum_const_zero]
      by_cases hx : ε i = true ∧ ε x = false
      · have hic : i ≠ c := fun h => by rw [h, hc'] at hx; exact Bool.noConfusion hx.1
        simp [modeWt, hx, root, Pi.single_apply, hic, Ne.symm hcx]
      · simp [modeWt, hx]
end ReciprocityTheory.ChartRestriction.DS
