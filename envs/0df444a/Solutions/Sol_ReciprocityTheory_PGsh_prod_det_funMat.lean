-- Prove2me | solution 1 for ReciprocityTheory.PGsh.prod_det_funMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:27:11.154961+00:00
-- url     : https://prove2.me/submissions/23d3503a-d0cf-4972-965b-8c19ca613d9c

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Theorems.Thm_ReciprocityTheory_PGsh_det_funMat_perm
import Theorems.Thm_ReciprocityTheory_PGsh_list_prod_funMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh
variable {n : ℕ}
namespace ReciprocityTheory.PGsh
theorem _root_.solution {s : ℕ} (σ : Equiv.Perm (Fin n)) (φ : Fin n → Fin s) :
    ∏ k, (funMat (fun b => if φ b = k then σ b else b)).det =
      if φ ∘ σ = φ then (Equiv.Perm.sign σ : ℤ) else 0 := by
  split_ifs with h
  · have hσ : ∀ b, φ (σ b) = φ b := fun b => congrFun h b
    have e := list_prod_funMat σ φ hσ (List.finRange s) (List.nodup_finRange s)
    have e2 : (funMat fun b => if φ b ∈ List.finRange s then σ b else b) = funMat σ := by
      congr 1; funext b; simp
    rw [e2] at e
    rw [← det_funMat_perm, ← e, ← List.prod_ofFn, List.ofFn_eq_map,
      show ∀ l : List (Matrix (Fin n) (Fin n) ℤ), l.prod.det = (l.map Matrix.det).prod from
        fun l => map_list_prod (Matrix.detMonoidHom) l, List.map_map]
    try rfl
  · have hex : ∃ b, φ (σ b) ≠ φ b := by
      by_contra hc
      push_neg at hc
      exact h (funext hc)
    obtain ⟨b, hb⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ (φ b))
    have hne : b ≠ σ b := fun e => hb (by rw [← e])
    apply Matrix.det_zero_of_column_eq hne
    intro a
    simp [funMat, hb]
end ReciprocityTheory.PGsh
