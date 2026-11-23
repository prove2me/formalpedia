-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.uw_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:18.940314+00:00
-- url     : https://prove2.me/submissions/cf0adb90-e324-476b-a959-b46df2687720

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_NilpotentSubgroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_uw_col_out
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_piI_not_inW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
noncomputable section
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
private lemma Hpk_applyUnitaryQuotientCompactness (i x : Fin (2 * r + k + 1)) :
    Hpk k r i x = if x = piI k r i then (if i.val = r + k then (-1 : ℂ) else 1) else 0 := by
  have hx := x.isLt
  have hi := i.isLt
  by_cases hW : r ≤ i.val ∧ i.val ≤ r + k
  · have hp : piI k r i = i := by
      unfold piI
      exact if_pos hW
    rw [hp]
    unfold Hpk
    have n1 : ¬ (i.val < r ∧ i.val + x.val = 2 * r + k) := by omega
    rw [if_neg n1]
    by_cases hxi : x = i
    · subst hxi
      have n2 : ¬ (x.val < r ∧ x.val + x.val = 2 * r + k) := by omega
      rw [if_neg n2, if_pos ⟨hW.1, hW.2, rfl⟩, if_pos rfl]
    · have hxv : x.val ≠ i.val := fun h => hxi (Fin.ext h)
      have n2 : ¬ (x.val < r ∧ i.val + x.val = 2 * r + k) := by omega
      have n3 : ¬ (r ≤ i.val ∧ i.val ≤ r + k ∧ i = x) := fun h => hxi h.2.2.symm
      rw [if_neg n2, if_neg n3, if_neg hxi]
  · have hp : piI k r i = ⟨2 * r + k - i.val, by omega⟩ := by
      unfold piI
      exact if_neg hW
    rw [hp]
    unfold Hpk
    have hc : ¬ (i.val = r + k) := by omega
    have n3 : ¬ (r ≤ i.val ∧ i.val ≤ r + k ∧ i = x) := fun h => hW ⟨h.1, h.2.1⟩
    rw [if_neg hc]
    by_cases hxi : x.val = 2 * r + k - i.val
    · have hx' : x = ⟨2 * r + k - i.val, by omega⟩ := Fin.ext hxi
      rw [if_pos hx']
      by_cases hir : i.val < r
      · rw [if_pos ⟨hir, by omega⟩]
      · have n1 : ¬ (i.val < r ∧ i.val + x.val = 2 * r + k) := fun h => hir h.1
        have p2 : x.val < r ∧ i.val + x.val = 2 * r + k := ⟨by omega, by omega⟩
        rw [if_neg n1, if_pos p2]
    · have hx' : ¬ x = ⟨2 * r + k - i.val, by omega⟩ := fun h => hxi (congrArg Fin.val h)
      have n1 : ¬ (i.val < r ∧ i.val + x.val = 2 * r + k) := by omega
      have n2 : ¬ (x.val < r ∧ i.val + x.val = 2 * r + k) := by omega
      rw [if_neg hx', if_neg n1, if_neg n2, if_neg n3]
private lemma piI_piI' (i : Fin (2 * r + k + 1)) : piI k r (piI k r i) = i := by
  by_cases hW : r ≤ i.val ∧ i.val ≤ r + k
  · have hp : piI k r i = i := by
      unfold piI
      exact if_pos hW
    rw [hp, hp]
  · have hi := i.isLt
    have hp : piI k r i = ⟨2 * r + k - i.val, by omega⟩ := by
      unfold piI
      exact if_neg hW
    rw [hp]
    have hW' : ¬ (r ≤ 2 * r + k - i.val ∧ 2 * r + k - i.val ≤ r + k) := by omega
    unfold piI
    rw [if_neg hW']
    apply Fin.ext
    show 2 * r + k - (2 * r + k - i.val) = i.val
    omega
end PI.QuotSetU.UnitaryGroupMassFormula.SW
end
end

set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
theorem _root_.solution {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (i j : Fin (2 * r + k + 1)) (hij : ¬ (inW k r i ∧ inW k r j)) :
    h i j = if i = j then 1 else 0 := by
  by_cases hj : inW k r j
  · have hi : ¬ inW k r i := fun h' => hij ⟨h', hj⟩
    have hne : i ≠ j := fun e => hi (by rw [e]; exact hj)
    rw [if_neg hne]
    have hh' := hh
    simp only [UWset, Set.mem_setOf_eq] at hh'
    have hU : hᴴ * Hpk k r * h = Hpk k r := hh'.1
    have hp := piI_not_inW hi
    have hcol : ∀ x, h x (piI k r i) = if x = piI k r i then 1 else 0 :=
      fun x => uw_col_out hh _ hp x
    have hrowp : ∀ y, (hᴴ * Hpk k r) (piI k r i) y = Hpk k r (piI k r i) y := by
      intro y
      rw [Matrix.mul_apply, Finset.sum_eq_single (piI k r i)]
      · rw [Matrix.conjTranspose_apply, hcol, if_pos rfl, star_one, one_mul]
      · intro x _ hx
        rw [Matrix.conjTranspose_apply, hcol, if_neg hx, star_zero, zero_mul]
      · intro hm
        exact absurd (Finset.mem_univ _) hm
    have e := congrFun (congrFun hU (piI k r i)) j
    rw [Matrix.mul_apply] at e
    simp only [hrowp] at e
    rw [Finset.sum_eq_single i] at e
    · rw [Hpk_applyUnitaryQuotientCompactness (piI k r i) i, Hpk_applyUnitaryQuotientCompactness (piI k r i) j, piI_piI', if_pos rfl,
        if_neg (Ne.symm hne)] at e
      have hc : (if (piI k r i).val = r + k then (-1 : ℂ) else 1) ≠ 0 := by
        split_ifs <;> norm_num
      exact (mul_eq_zero.mp e).resolve_left hc
    · intro y _ hy
      rw [Hpk_applyUnitaryQuotientCompactness (piI k r i) y, piI_piI', if_neg hy, zero_mul]
    · intro hm
      exact absurd (Finset.mem_univ _) hm
  · exact uw_col_out hh j hj i
end PI.QuotSetU.UnitaryGroupMassFormula.SW
