-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.inv_fix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:38.630791+00:00
-- url     : https://prove2.me/submissions/71ff09de-a8a5-4dd3-8a6d-5e4b24bb68ef

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_NilpotentSubgroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
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
private lemma sign_mul_sign_piI_eq_one (i : Fin (2 * r + k + 1)) :
    (if i.val = r + k then (-1 : ℂ) else 1) *
      (if (piI k r i).val = r + k then (-1 : ℂ) else 1) = 1 := by
  by_cases hW : r ≤ i.val ∧ i.val ≤ r + k
  · have hp : piI k r i = i := by
      unfold piI
      exact if_pos hW
    rw [hp]
    split_ifs <;> norm_num
  · have hi := i.isLt
    have hp : piI k r i = ⟨2 * r + k - i.val, by omega⟩ := by
      unfold piI
      exact if_neg hW
    rw [hp]
    have h1 : ¬ (i.val = r + k) := by omega
    have h2 : ¬ ((⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1)).val = r + k) := by
      show ¬ (2 * r + k - i.val = r + k)
      omega
    rw [if_neg h1, if_neg h2, one_mul]
private lemma Hpk_mul_Hpk : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply, Finset.sum_eq_single (piI k r i)]
  · rw [Hpk_applyUnitaryQuotientCompactness i (piI k r i), if_pos rfl, Hpk_applyUnitaryQuotientCompactness (piI k r i) j, piI_piI']
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl, sign_mul_sign_piI_eq_one]
    · rw [if_neg (Ne.symm hij), if_neg hij, mul_zero]
  · intro x _ hx
    rw [Hpk_applyUnitaryQuotientCompactness i x, if_neg hx, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
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
theorem _root_.solution {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hU : a ∈ UH (Hpk k r))
    {v : Fin (2 * r + k + 1) → ℂ} (hv : a *ᵥ v = v) : a⁻¹ *ᵥ v = v := by
  have hU' : aᴴ * Hpk k r * a = Hpk k r := hU
  have hl : (Hpk k r * aᴴ * Hpk k r) * a = 1 := by
    calc Hpk k r * aᴴ * Hpk k r * a = Hpk k r * (aᴴ * Hpk k r * a) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU', Hpk_mul_Hpk]
  rw [Matrix.inv_eq_left_inv hl]
  calc (Hpk k r * aᴴ * Hpk k r) *ᵥ v = (Hpk k r * aᴴ * Hpk k r) *ᵥ (a *ᵥ v) := by rw [hv]
    _ = v := by rw [Matrix.mulVec_mulVec, hl, Matrix.one_mulVec]
end PI.QuotSetU.UnitaryGroupMassFormula.SW
