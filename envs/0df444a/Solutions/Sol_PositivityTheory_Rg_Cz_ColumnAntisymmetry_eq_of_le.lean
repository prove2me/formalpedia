-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ColumnAntisymmetry.eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:14.256003+00:00
-- url     : https://prove2.me/submissions/20b4099a-b330-4a3a-933c-6b12dc5c6854

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiB
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_rk_le
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_sum_rk
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_npairs_le
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
theorem _root_.solution {m : ℕ} (col : Fin m → ℕ) (top : Fin n) (htop : (top : ℕ) + 1 = n) (b I : Fin m → Fin n)
    (hb : IsTab col b) (hI : ColInj col I) (h : ∑ p, ((top : ℕ) - I p) ≤ npairs col) :
    ∃ σ ∈ colG col, I = b ∘ σ := by
  classical
  have heq : ∀ p, rk col I p = (top : ℕ) - I p := by
    have hs : ∑ p, rk col I p = ∑ p, ((top : ℕ) - I p) :=
      le_antisymm (by rw [sum_rk col I hI]; exact npairs_le col top htop I hI) (by rw [sum_rk col I hI]; exact h)
    intro p
    exact (Finset.sum_eq_sum_iff_of_le (fun p _ => rk_le col top htop I hI p)).mp hs p (Finset.mem_univ p)
  have hex : ∀ p, ∃ q, col q = col p ∧ b q = I p := by
    intro p
    have hA : (top : ℕ) - I p + 1 ≤ (Finset.univ.filter fun q => col q = col p).card := by
      rw [← heq p]
      unfold rk
      rw [← Finset.card_insert_of_notMem (s := Finset.univ.filter fun q => col q = col p ∧ I p < I q) (a := p) (by simp)]
      apply Finset.card_le_card
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rcases hq with rfl | hq
      · rfl
      · exact hq.1
    by_cases hb0 : ∃ q, col q = col p ∧ b q ≤ I p
    · obtain ⟨q0, hq0c, hq0b⟩ := hb0
      rcases lt_or_eq_of_le hq0b with hlt | heq'
      · obtain ⟨q, hqc, hqb⟩ := hb.2 q0 (I p) hlt
        exact ⟨q, hqc.trans hq0c, hqb⟩
      · exact ⟨q0, hq0c, heq'⟩
    · push_neg at hb0
      exfalso
      have hB : (Finset.univ.filter fun q => col q = col p).card ≤ (Finset.Ioi (I p)).card := by
        apply Finset.card_le_card_of_injOn b
        · intro q hq
          simp at hq ⊢
          exact hb0 q hq
        · intro q hq q' hq' hqq
          simp at hq hq'
          exact hb.1 q q' (hq.trans hq'.symm) hqq
      rw [Fin.card_Ioi] at hB
      have := (I p).isLt
      omega
  choose σf hσc hσb using hex
  have hinj : Function.Injective σf := by
    intro p p' hpp
    have hc : col p = col p' := by rw [← hσc p, ← hσc p', hpp]
    have hi : I p = I p' := by rw [← hσb p, ← hσb p', hpp]
    exact hI p p' hc hi
  let σ : Equiv.Perm (Fin m) := Equiv.ofBijective σf (Finite.injective_iff_bijective.mp hinj)
  refine ⟨σ, ?_, ?_⟩
  · simp [colG, σ, hσc]
  · funext p
    simp [σ, hσb]
end PositivityTheory.Rg.Cz.ColumnAntisymmetry
