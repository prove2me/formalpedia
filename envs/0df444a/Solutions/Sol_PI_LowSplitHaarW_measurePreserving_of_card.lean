-- Prove2me | solution 1 for PI.LowSplitHaarW.measurePreserving_of_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:58:24.59635+00:00
-- url     : https://prove2.me/submissions/c6fb5818-0691-489c-9132-585519ef909c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerShearHaar_TriShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerShearHaar_MeasurePreservingOfCard
import Theorems.Thm_PI_LowSplitHaarW_measurable_extNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
open PI PI.LowSplitHaarW
namespace PI.LowSplitHaarW
theorem _root_.solution (n : ℕ) : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ (r : ι → ℕ) (g : ι → (ι → ℂ) → ℂ), (∀ i, Measurable (g i)) →
    (∀ i (x y : ι → ℂ), (∀ j, r j < r i → x j = y j) → g i x = g i y) →
    MeasurePreserving (fun x : ι → ℂ => fun i => x i + g i x) volume volume := by
  induction n with
  | zero =>
    intro ι _ _ hcard r g _ _
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.1 hcard
    have : (fun x : ι → ℂ => fun i => x i + g i x) = id := by
      funext x i
      exact isEmptyElim i
    rw [this]
    exact MeasurePreserving.id _
  | succ n ih =>
    intro ι _ _ hcard r g hg hdep
    haveI : Nonempty ι := Fintype.card_pos_iff.1 (by omega)

    obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ r Finset.univ_nonempty
    have hja : ∀ i j, r j < r i → j ≠ a := by
      rintro i j hj rfl
      exact absurd (ha i (Finset.mem_univ _)) (not_le.2 hj)
    have hext : ∀ (x : ι → ℂ) (i : ι), g i x = g i (extNe a (fun j : {j // j ≠ a} => x j)) := by
      intro x i
      refine hdep i _ _ fun j hj => ?_
      simp [extNe, hja i j hj]
    have hcard' : Fintype.card {j // j ≠ a} = n := by
      simp [Fintype.card_subtype_compl, hcard]

    have hF := ih {j // j ≠ a} hcard' (fun j => r j) (fun j y => g j (extNe a y))
      (fun j => (hg j).comp (measurable_extNe a)) (by
        intro j y z hyz
        refine hdep j _ _ fun l hl => ?_
        by_cases h : l ≠ a
        · simp only [extNe, dif_pos h]
          exact hyz ⟨l, h⟩ hl
        · simp only [extNe, dif_neg h])
    let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun j => j ≠ a)
    have he : MeasurePreserving e volume volume :=
      volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun j => j ≠ a)

    have hG := hF.skew_product (g := fun y (z : {j // ¬ j ≠ a} → ℂ) => fun q => z q + g a (extNe a y))
      (by
        refine measurable_pi_lambda _ fun q => ?_
        exact ((measurable_pi_apply q).comp measurable_snd).add
          ((hg a).comp ((measurable_extNe a).comp measurable_fst)))
      (Filter.Eventually.of_forall fun y =>
        (measurePreserving_add_right (volume : Measure ({j // ¬ j ≠ a} → ℂ))
          (fun _ => g a (extNe a y))).map_eq)
    have key : (fun x : ι → ℂ => fun i => x i + g i x) =
        e.symm ∘ (fun p => ((fun i : {j // j ≠ a} => p.1 i + g i (extNe a p.1)),
          fun q : {j // ¬ j ≠ a} => p.2 q + g a (extNe a p.1))) ∘ e := by
      funext x i
      by_cases h : i ≠ a
      · simp [e, h, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hext x i]
      · have h' : i = a := not_not.1 h
        subst h'
        simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hext x i]
    rw [key]
    exact he.symm.comp (hG.comp he)
end PI.LowSplitHaarW
