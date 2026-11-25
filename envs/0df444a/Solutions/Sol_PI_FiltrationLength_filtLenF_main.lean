-- Prove2me | solution 1 for PI.FiltrationLength.filtLenF_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:46:47.425623+00:00
-- url     : https://prove2.me/submissions/e630322d-ffbd-4361-bf8c-fadd6602902c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FiltLen
import Definitions.Def_Formalism_PeriodIntegrals_FiltLenF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiltrationLength_LengthQuotLeOfKerLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiltrationLength_FiltLenFMain
import Theorems.Thm_PI_FiltrationLength_ell_stepF
import Theorems.Thm_PI_FiltrationLength_ell_add
import Theorems.Thm_PI_FiltrationLength_ell_sup_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FiltrationLength
open Submodule
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]
namespace PI.FiltrationLength
theorem _root_.solution : PI.FiltLenF := by
  intro R W _ _ _ F a hanti h0 ha V _ _ φ hinj M N P Q hNM hP hQ
  set X : ℕ → Submodule R W := fun k => N ⊔ (M ⊓ F k) with hX
  have hXmono : ∀ k, X (k + 1) ≤ X k := fun k =>
    sup_le_sup_left (inf_le_inf_left _ (hanti (Nat.le_succ k))) _
  have hX0 : X 0 = M := by simp [hX, h0, sup_eq_right.2 hNM]
  have hXa : X a = N := by simp [hX, ha]
  have hXle0 : ∀ k, X k ≤ X 0 := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hXmono k).trans ih
  have hstep : ∀ k < a, ell (X k) (X (k + 1)) ≤
      Module.length R (↥(P k) ⧸ (Q k).comap (P k).subtype) := by
    intro k hk
    have hD : (N ⊓ F k) ⊔ (M ⊓ F (k + 1)) ≤ X (k + 1) :=
      sup_le (inf_le_left.trans le_sup_left) le_sup_right
    have heq : X (k + 1) ⊔ (M ⊓ F k) = X k := by
      simp only [hX]
      apply le_antisymm
      · exact sup_le (sup_le le_sup_left
          (le_sup_of_le_right (inf_le_inf_left _ (hanti (Nat.le_succ k))))) le_sup_right
      · exact sup_le (le_sup_of_le_left le_sup_left) le_sup_right
    have h1 : ell (X k) (X (k + 1)) ≤ ell (M ⊓ F k) ((N ⊓ F k) ⊔ (M ⊓ F (k + 1))) := by
      calc ell (X k) (X (k + 1)) = ell (X (k + 1) ⊔ (M ⊓ F k)) (X (k + 1)) := by rw [heq]
        _ ≤ _ := ell_sup_le hD
    exact h1.trans (ell_stepF M N (F k) (F (k + 1)) (φ k) (P k) (Q k) hNM (hinj k) (hP k hk) (hQ k hk))
  have hsum : ∀ j ≤ a, ell (X 0) (X j) ≤
      ∑ k ∈ Finset.range j, Module.length R (↥(P k) ⧸ (Q k).comap (P k).subtype) := by
    intro j
    induction j with
    | zero => intro _; simp [ell, Submodule.comap_subtype_self]
    | succ j ih =>
      intro hj
      rw [ell_add (hXmono j) (hXle0 j), Finset.sum_range_succ, add_comm]
      exact add_le_add (ih (Nat.le_of_succ_le hj)) (hstep j hj)
  have hfin := hsum a le_rfl
  rw [hX0, hXa] at hfin
  exact hfin
end PI.FiltrationLength
