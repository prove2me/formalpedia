-- Prove2me | solution 1 for RH.Transport.PhysicalHigh.distinct_slots_for_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:59:41.857161+00:00
-- url     : https://prove2.me/submissions/5f0408e2-eebc-45f0-8f85-0ffdd28aed4a

import Definitions.Def_OAI_NumberTheory_DirichletL_ParametersSlotLengths
import Definitions.Def_Transport_PhysicalHigh_DistinctSlots

set_option autoImplicit false
open RH RH.Transport RH.Transport.PhysicalHigh
noncomputable section
open scoped BigOperators
namespace RH.Transport.PhysicalHigh
theorem _root_.solution (total : ℝ) (htotal : 0 < total)
    (K : ℕ) (hK : 0 < K) :
    ∃ ell : Fin K → ℝ, Function.Injective ell ∧
      (∑ j, ell j) = total ∧
      (∀ j, total / (2 * K) ≤ ell j ∧ ell j < 2 * total / K) := by
  have hKp : 0 < (K : ℝ) := by exact_mod_cast hK
  let w : Fin K → ℝ := fun j => 1 + (j.val : ℝ) / K
  let A : ℝ := ∑ j, w j
  have hw (j : Fin K) : 1 ≤ w j ∧ w j < 2 := by
    have hj : (j.val : ℝ) < K := by exact_mod_cast j.isLt
    have hdiv : (j.val : ℝ) / K < 1 := (div_lt_one hKp).mpr hj
    dsimp only [w]
    constructor
    · linarith [div_nonneg (Nat.cast_nonneg j.val) hKp.le]
    · linarith
  have hAlo : (K : ℝ) ≤ A := by
    calc
      _ = ∑ _j : Fin K, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => (hw j).1
  have hAhi : A ≤ 2 * K := by
    calc
      _ ≤ ∑ _j : Fin K, (2 : ℝ) := Finset.sum_le_sum fun j _ => (hw j).2.le
      _ = _ := by simp; ring
  have hAp : 0 < A := hKp.trans_le hAlo
  let ell : Fin K → ℝ := fun j => total * w j / A
  refine ⟨ell, ?_, ?_, ?_⟩
  · intro j k he
    have hmul : total * w j = total * w k := (div_left_inj' hAp.ne').mp he
    have hwjk : w j = w k := mul_left_cancel₀ htotal.ne' hmul
    have hjk : (j.val : ℝ) / K = (k.val : ℝ) / K := by
      dsimp [w] at hwjk
      linarith
    have he' : (j.val : ℝ) = (k.val : ℝ) := (div_left_inj' hKp.ne').mp hjk
    apply Fin.ext
    exact_mod_cast he'
  · dsimp only [ell]
    rw [← Finset.sum_div, ← Finset.mul_sum]
    change total * A / A = total
    exact mul_div_cancel_right₀ total hAp.ne'
  · intro j
    constructor
    · calc
        total / (2 * K) ≤ total / A :=
          div_le_div_of_nonneg_left htotal.le hAp hAhi
        _ ≤ total * w j / A :=
          div_le_div_of_nonneg_right (by nlinarith [(hw j).1]) hAp.le
    · calc
        ell j < 2 * total / A :=
          (div_lt_div_iff_of_pos_right hAp).mpr (by nlinarith [(hw j).2])
        _ ≤ 2 * total / K :=
          div_le_div_of_nonneg_left (by positivity) hKp hAlo
end RH.Transport.PhysicalHigh
