-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ColumnAntisymmetry.Q_colG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:42:16.410874+00:00
-- url     : https://prove2.me/submissions/461bfb4d-6d22-45cc-81b5-baef11fe8d18

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAnti
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_Q_mul
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_Q_one
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
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {m : ℕ}
namespace PositivityTheory.Rg.Cz.ColumnAntisymmetry
theorem _root_.solution (L : TV n M (Fin m) →ₗ[ℂ] ℂ) (col : Fin m → ℕ)
    (hsw : ∀ p q : Fin m, p ≠ q → col p = col q → Q L (Equiv.swap p q)) :
    ∀ σ ∈ colG col, Q L σ := by
  intro σ hσ
  induction h : σ.support.card using Nat.strong_induction_on generalizing σ with
  | _ k ih =>
    by_cases h1 : σ = 1
    · rw [h1]; exact Q_one L
    · obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
        by_contra hh; push Not at hh; exact h1 (Equiv.ext hh)
      have hmem : ∀ p, col (σ p) = col p := by simpa [colG] using hσ
      have hτ : Equiv.swap x (σ x) * σ ∈ colG col := by
        simp only [colG, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.mul_apply]
        intro p
        rw [Equiv.swap_apply_def]
        split_ifs with e1 e2
        · rw [hmem x, ← e1, hmem]
        · rw [← hmem x, ← e2, hmem]
        · exact hmem p
      have hlt := Equiv.Perm.card_support_swap_mul hx
      have hq := ih _ (h ▸ hlt) _ hτ rfl
      have hs := hsw x (σ x) hx.symm (hmem x).symm
      have := Q_mul L hs hq
      rwa [← mul_assoc, Equiv.swap_mul_self, one_mul] at this
end PositivityTheory.Rg.Cz.ColumnAntisymmetry
