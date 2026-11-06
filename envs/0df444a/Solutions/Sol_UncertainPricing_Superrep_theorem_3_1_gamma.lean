-- Prove2me | solution 1 for UncertainPricing.Superrep.theorem_3_1_gamma
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T18:48:31.740078+00:00
-- url     : https://prove2.me/submissions/da354f3f-4194-4cf5-9945-46fede3290f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UncertainPricing_Superrep_Setting
import Definitions.Def_UncertainPricing_Superrep_Compact
import Theorems.Thm_UncertainPricing_Superrep_representation_sec5
import Theorems.Thm_UncertainPricing_Superrep_proposition_5_2
import Theorems.Thm_UncertainPricing_Superrep_lemma_5_3

open MeasureTheory Filter Topology BoundedContinuousFunction
open UncertainPricing.Superrep

theorem solution (T : ℝ) (hT : 0 < T) (μL μU : StieltjesFunction ℝ) (hμL : IsDistFn T μL)
    (hμU : IsDistFn T μU) (Ps : Set (Measure (Ω T)))
    (hPs : ∀ P ∈ Ps, IsMartingaleMeasure P ∧ HypLU μL μU P)
    (hHol : IsHolder T μU) :
    ∃ P'' : Set (Measure (Ω T)), (∀ P ∈ P'', IsMartingaleMeasure P ∧ HypLU μL μU P) ∧
      ∀ f : Ω T →ᵇ ℝ, InGamma Ps μU f → Lam Ps μU f = supE P'' f := by
  have hPsU : ∀ P ∈ Ps, IsMartingaleMeasure P ∧ HypU μU P := by
    intro P hP
    obtain ⟨hm, A, hA, hAe⟩ := hPs P hP
    exact ⟨hm, A, hA, hAe.mono fun ω h s t hst => (h s t hst).2⟩
  -- `𝐏'' = {Q* : Q ∈ 𝒬}`, the laws of the continuous modifications of `B̃`
  refine ⟨{P | ∃ Q ∈ Qset Ps μU, ∃ X : Set.Icc (0 : ℝ) T → Ωt T → ℝ,
      ∃ hX : IsContModif Q X, P = lawOf Q hX}, ?_, ?_⟩
  · rintro P ⟨Q, hQ, X, hX, rfl⟩
    exact lemma_5_3 T hT μL μU hμL hμU Ps hPs hHol Q hQ X hX
  · intro f hf
    rw [representation_sec5 T hT μU hμU Ps hPsU hHol f]
    unfold supE
    apply le_antisymm
    · refine iSup₂_le fun Q hQ => ?_
      obtain ⟨-, -, X, hX⟩ := proposition_5_2 T hT μU hμU Ps hPsU hHol Q hQ
      rw [hf Q hQ X hX]
      exact le_iSup₂_of_le (f := fun P (_ : P ∈ {P | ∃ Q ∈ Qset Ps μU,
        ∃ X : Set.Icc (0 : ℝ) T → Ωt T → ℝ, ∃ hX : IsContModif Q X, P = lawOf Q hX}) =>
          ((∫ ω, f ω ∂P : ℝ) : EReal)) (lawOf Q hX) ⟨Q, hQ, X, hX, rfl⟩ le_rfl
    · refine iSup₂_le ?_
      rintro P ⟨Q, hQ, X, hX, rfl⟩
      rw [← hf Q hQ X hX]
      exact le_iSup₂_of_le (f := fun Q (_ : Q ∈ Qset Ps μU) =>
        ((∫ x, ext f x ∂Q : ℝ) : EReal)) Q hQ le_rfl
