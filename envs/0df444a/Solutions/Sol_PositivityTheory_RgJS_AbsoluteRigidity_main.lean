-- Prove2me | solution 1 for PositivityTheory.RgJS.AbsoluteRigidity.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:07:51.729729+00:00
-- url     : https://prove2.me/submissions/dace985b-008d-4808-99c6-bbe8827528e0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_AbsoluteRigidityLemma_AbsoluteRigidityOfCommon
import Theorems.Thm_PositivityTheory_RgJS_AbsoluteRigidity_rel_remove
import Theorems.Thm_PositivityTheory_RgJS_AbsoluteRigidity_exists_common

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgJS
open PositivityTheory.RgJS.AbsoluteRigidity
variable {W : Type} {q : W → ℕ} {X : Type} {d : X → ℕ} {A : ∀ x, W → Fin (d x) → ℂ}
namespace PositivityTheory.RgJS.AbsoluteRigidity
theorem _root_.solution (hC : Common0) (hS : Sys q X d A) : ∀ (N : ℕ) (ι κ : Type) [Fintype ι] [Fintype κ]
    (x : ι → X × ℝ) (y : κ → X × ℝ), Fintype.card ι + Fintype.card κ ≤ N → Rel q A x y →
      ∃ s : ι ≃ κ, ∀ i, x i = y (s i) := by
  intro N
  induction N with
  | zero =>
    intro ι κ _ _ x y hN _
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 (by omega)
    have : IsEmpty κ := Fintype.card_eq_zero_iff.1 (by omega)
    exact ⟨Equiv.equivOfIsEmpty ι κ, fun i => isEmptyElim i⟩
  | succ N ih =>
    intro ι κ _ _ x y hN h
    classical
    have step : Nonempty ι ∨ Nonempty κ → ∃ s : ι ≃ κ, ∀ i, x i = y (s i) := by
      intro hne
      obtain ⟨i, j, hij⟩ := exists_common hC hS x y h hne
      have hr := rel_remove h i j hij
      have c1 : Fintype.card {i' // i' ≠ i} < Fintype.card ι := Fintype.card_subtype_lt (p := fun i' => i' ≠ i) (x := i) (by simp)
      have c2 : Fintype.card {j' // j' ≠ j} < Fintype.card κ := Fintype.card_subtype_lt (p := fun j' => j' ≠ j) (x := j) (by simp)
      obtain ⟨s', hs'⟩ := ih {i' // i' ≠ i} {j' // j' ≠ j} (fun i' => x i') (fun j' => y j') (by omega) hr
      refine ⟨(Equiv.optionSubtypeNe i).symm.trans ((Equiv.optionCongr s').trans (Equiv.optionSubtypeNe j)), fun i' => ?_⟩
      by_cases hi : i' = i
      · subst hi
        simp only [Equiv.trans_apply, Equiv.optionSubtypeNe_symm_self, Equiv.optionCongr_apply, Option.map_none,
          Equiv.optionSubtypeNe_none]
        exact hij
      · simp only [Equiv.trans_apply, Equiv.optionSubtypeNe_symm_of_ne hi, Equiv.optionCongr_apply, Option.map_some,
          Equiv.optionSubtypeNe_some]
        exact hs' ⟨i', hi⟩
    rcases isEmpty_or_nonempty ι with hι | hι
    · rcases isEmpty_or_nonempty κ with hκ | hκ
      · exact ⟨Equiv.equivOfIsEmpty ι κ, fun i => isEmptyElim i⟩
      · exact step (Or.inr hκ)
    · exact step (Or.inl hι)
end PositivityTheory.RgJS.AbsoluteRigidity
