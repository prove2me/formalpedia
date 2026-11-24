-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ColumnAntisymmetry.sum_rk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:45.280435+00:00
-- url     : https://prove2.me/submissions/2239b41c-729e-4969-a032-61d43eecac01

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiB
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.ColumnAntisymmetry
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.ColumnAntisymmetry
theorem _root_.solution {m : ℕ} (col : Fin m → ℕ) (I : Fin m → Fin n) (hI : ColInj col I) :
    ∑ p, rk col I p = npairs col := by
  have e1 : ∑ p, rk col I p = (Finset.univ.filter fun x : Fin m × Fin m => col x.2 = col x.1 ∧ I x.1 < I x.2).card := by
    unfold rk
    simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [e1]
  unfold npairs
  apply Finset.card_bij' (fun x _ => if x.1 < x.2 then x else x.swap) (fun y _ => if I y.1 < I y.2 then y else y.swap)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    by_cases h : x.1 < x.2
    · simp [h, hx.2]
    · have h' : ¬ I x.2 < I x.1 := not_lt.mpr hx.2.le
      simp [h, h']
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    by_cases h : I y.1 < I y.2
    · simp [h, hy.1]
    · have h' : ¬ y.2 < y.1 := not_lt.mpr hy.1.le
      simp [h, h']
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have hne : x.1 ≠ x.2 := fun h => by rw [h] at hx; exact lt_irrefl _ hx.2
    split_ifs with h
    · exact ⟨h, hx.1.symm⟩
    · try simp only [Prod.fst_swap, Prod.snd_swap]
      refine ⟨?_, hx.1⟩
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact absurd h' h
      · exact h'
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have hne : I y.1 ≠ I y.2 := fun h => (ne_of_lt hy.1) (hI _ _ hy.2 h)
    split_ifs with h
    · exact ⟨hy.2.symm, h⟩
    · try simp only [Prod.fst_swap, Prod.snd_swap]
      exact ⟨hy.2, lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne)⟩
end PositivityTheory.Rg.Cz.ColumnAntisymmetry
