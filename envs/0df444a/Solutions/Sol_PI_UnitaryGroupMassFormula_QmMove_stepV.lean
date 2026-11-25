-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.stepV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:03:52.794933+00:00
-- url     : https://prove2.me/submissions/51544667-e276-4477-9f43-bfd064e2087f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_MoveOperatorCovariance
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermsSignSquared
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_symV_comm
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_midV
import Theorems.Thm_Formalism_REAL_drop_ofFn_congr
import Theorems.Thm_Formalism_REAL_take_ofFn_congr
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_prod_diff
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_step


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmMove
variable {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (y : Fin n → A)
  (a : Fin m → Fin n) (b : Fin (m + 1) → Fin n) (w : ℂ)
namespace PI.UnitaryGroupMassFormula.QmMove
theorem _root_.solution (hy : ∀ a b c, E a b * y c - y c * E a b = if a = c then -y b else 0)
    (p : ℕ) (hp : p < m) : Mv E y a b w (p + 1) = -Mv E y a b w p := by
  set s : Equiv.Perm (Fin (m + 1)) := Equiv.swap ⟨p, by omega⟩ ⟨p + 1, by omega⟩ with hs_def
  have hs : Equiv.Perm.sign s = -1 := Equiv.Perm.sign_swap (by simp [Fin.ext_iff])
  have hfix : ∀ q : Fin (m + 1), (q : ℕ) ≠ p → (q : ℕ) ≠ p + 1 → s q = q := by
    intro q h1 h2
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h; apply h1; rw [h]
    · intro h; apply h2; rw [h]
  have hoff : ∀ τ σ (q : Fin (m + 1)), (q : ℕ) ≠ p → (q : ℕ) ≠ p + 1 →
      Fv E y a b w p (τ * s) σ q = Fv E y a b w p τ σ q := by
    intro τ σ q h1 h2
    simp only [Fv, Equiv.Perm.mul_apply, hfix q h1 h2]
  have hoff2 : ∀ τ σ (q : Fin (m + 1)), (q : ℕ) ≠ p → (q : ℕ) ≠ p + 1 →
      Fv E y a b w (p + 1) τ σ q = Fv E y a b w p τ σ q := by
    intro τ σ q h1 h2
    have e1 : ((q : ℕ) < p + 1) ↔ ((q : ℕ) < p) := by omega
    simp only [Fv, if_neg h1, if_neg h2, e1]
  have htk : ∀ τ σ, (List.ofFn (Fv E y a b w p (τ * s) σ)).take p =
      (List.ofFn (Fv E y a b w p τ σ)).take p :=
    fun τ σ => take_ofFn_congr _ _ p (fun k hk => hoff τ σ k (by omega) (by omega))
  have hdr : ∀ τ σ, (List.ofFn (Fv E y a b w p (τ * s) σ)).drop (p + 2) =
      (List.ofFn (Fv E y a b w p τ σ)).drop (p + 2) :=
    fun τ σ => drop_ofFn_congr _ _ (p + 2) (fun k hk => hoff τ σ k (by omega) (by omega))
  have hsp : s ⟨p, by omega⟩ = ⟨p + 1, by omega⟩ := Equiv.swap_apply_left _ _
  have hsp1 : s ⟨p + 1, by omega⟩ = ⟨p, by omega⟩ := Equiv.swap_apply_right _ _
  have n1 : p + 1 ≠ p := by omega
  have n2 : p < p + 1 := by omega
  have n3 : ¬ (p + 1 < p) := by omega
  have n4 : p + 1 - 1 = p := by omega
  refine step s hs (fun τ => Pv E y a b w p τ) (fun τ => Pv E y a b w (p + 1) τ)
    (fun τ => ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : A) *
      (((List.ofFn (Fv E y a b w p τ σ)).take p).prod *
        symV y (extN (a ∘ σ) (b 0) p) (b (τ ⟨p + 1, by omega⟩)) (b (τ ⟨p, by omega⟩)) *
        ((List.ofFn (Fv E y a b w p τ σ)).drop (p + 2)).prod)) ?_ ?_
  · intro τ
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    simp only [htk, hdr, Equiv.Perm.mul_apply, hsp, hsp1]
    rw [symV_comm]
  · intro τ
    simp only [Pv]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [← mul_sub, prod_diff _ _ p (by omega)
      (fun k h1 h2 => (hoff2 τ σ k h1 h2).trans (hoff τ σ k h1 h2).symm), htk, hdr]
    congr 1
    congr 2
    simp only [Fv, Equiv.Perm.mul_apply, hsp, hsp1, if_true, if_neg n1, if_pos n2, if_neg n3, n4,
      if_neg n1.symm]
    exact midV E y hy _ _ (by push_cast; ring) _ _ _
end PI.UnitaryGroupMassFormula.QmMove
