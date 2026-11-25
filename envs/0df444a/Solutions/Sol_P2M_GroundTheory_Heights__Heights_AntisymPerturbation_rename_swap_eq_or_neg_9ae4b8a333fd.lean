-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AntisymPerturbation_rename_swap_eq_or_neg_9ae4b8a333fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:36:27.129292+00:00
-- url     : https://prove2.me/submissions/bff74973-6280-4eb3-a864-5fd7c229bb41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymPerturbation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymPerturbation_rename_mul_eq_or_neg_9d0bf095579c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.AntisymPerturbation
variable {T : Type} [Fintype T] [DecidableEq T] {N j : ℕ}
namespace GroundTheory.Heights₂.Heights.AntisymPerturbation
theorem _root_.solution {R : MvPolynomial (T × Fin N) ℝ} (hR : R ∈ antisymSpace T N j)
    (τ : T) (a c : Fin N) (hac : a.val ≤ c.val) (hblk : c.val < j ∨ j ≤ a.val) :
    rename ⇑(Equiv.swap (τ, a) (τ, c)) R = R ∨ rename ⇑(Equiv.swap (τ, a) (τ, c)) R = -R := by
  have hR' : ∀ σ, IsBlockSimpleSwap T N j σ → rename σ R = -R := hR.2
  suffices H : ∀ k : ℕ, ∀ c : Fin N, c.val = a.val + k → (c.val < j ∨ j ≤ a.val) →
      rename ⇑(Equiv.swap (τ, a) (τ, c)) R = R ∨ rename ⇑(Equiv.swap (τ, a) (τ, c)) R = -R from
    H (c.val - a.val) c (by omega) hblk
  intro k
  induction k with
  | zero =>
    intro c hc _
    have hca : c = a := Fin.ext (by omega)
    subst hca
    left
    rw [Equiv.swap_self, Equiv.coe_refl, rename_id_apply]
  | succ k ih =>
    intro c hc hb
    have hc' : a.val + k < N := by omega
    have hsimple : rename ⇑(Equiv.swap (τ, (⟨a.val + k, hc'⟩ : Fin N)) (τ, c)) R = -R :=
      hR' _ ⟨τ, ⟨a.val + k, hc'⟩, c, by simp only; omega, by simp only; omega, rfl⟩
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have hca : (⟨a.val + 0, hc'⟩ : Fin N) = a := Fin.ext (by simp)
      rw [hca] at hsimple
      exact Or.inr hsimple
    · have hprev := ih ⟨a.val + k, hc'⟩ rfl (by simp only; omega)
      have h1 : (τ, a) ≠ (τ, (⟨a.val + k, hc'⟩ : Fin N)) := by
        simp only [ne_eq, Prod.mk.injEq, true_and, Fin.ext_iff]; omega
      have h2 : (τ, a) ≠ (τ, c) := by
        simp only [ne_eq, Prod.mk.injEq, true_and, Fin.ext_iff]; omega
      have e := Equiv.swap_mul_swap_mul_swap h1 h2
      rw [Equiv.swap_comm (τ, c) (τ, a)] at e
      rw [← e]
      exact rename_mul_eq_or_neg (rename_mul_eq_or_neg (Or.inr hsimple) hprev) (Or.inr hsimple)
end GroundTheory.Heights₂.Heights.AntisymPerturbation
