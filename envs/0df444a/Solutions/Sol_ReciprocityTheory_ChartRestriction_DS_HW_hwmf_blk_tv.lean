-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.hwmf_blk_tv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:13:43.892179+00:00
-- url     : https://prove2.me/submissions/02aaada8-b426-4dee-9ca0-391f0a3b864c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_hwmf_mul_tv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) (c : Fin n)
    (x : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    blkMinor ε c (x * (1 + s • single a b (1 : ℂ))) = blkMinor ε c x := by
  unfold blkMinor
  by_cases hb : ε b = ε c ∧ b ≤ c
  · obtain ⟨B, hB⟩ : ∃ B : {d : Fin n // ε d = ε c ∧ d ≤ c}, (B : Fin n) = b := ⟨⟨b, hb⟩, rfl⟩
    obtain ⟨A, hA⟩ : ∃ A : {d : Fin n // ε d = ε c ∧ d ≤ c}, (A : Fin n) = a :=
      ⟨⟨a, he.trans hb.1, hab.le.trans hb.2⟩, rfl⟩
    have hBA : B ≠ A := fun h => (ne_of_lt hab) (by rw [← hA, ← hB, h])
    have hM : (x * (1 + s • single a b (1 : ℂ))).submatrix
        (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) =
        (x.submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n))).updateCol B
          (fun k => x.submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) k B +
            s • x.submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) k A) := by
      ext i j
      rw [Matrix.submatrix_apply, hwmf_mul_tv, Matrix.updateCol_apply]
      by_cases hj : j = B
      · subst hj
        simp [hB, hA, smul_eq_mul]
      · have hj' : (j : Fin n) ≠ b := fun h => hj (Subtype.ext (h.trans hB.symm))
        simp [hj, hj']
    rw [hM, Matrix.det_updateCol_add_smul_self _ hBA]
  · congr 1
    ext i j
    rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hwmf_mul_tv]
    have hj : (j : Fin n) ≠ b := fun h => hb (h ▸ j.2)
    simp [hj]
end ReciprocityTheory.ChartRestriction.DS.HW
