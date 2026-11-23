-- Prove2me | solution 1 for TIESharp.theorem_3_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:50:12.352923+00:00
-- url     : https://prove2.me/submissions/792251e2-7ff8-479b-8816-f7217f29ad25
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TIESharp_IsFeasible
import Definitions.Def_TIESharp_IsTIE
import Definitions.Def_TIESharp_IsRApprox
import Theorems.Thm_TIESharp_lemma_4_1
import Theorems.Thm_TIESharp_lemma_4_2
import Theorems.Thm_TIESharp_lemma_4_3
import Theorems.Thm_TIESharp_lemma_4_4
import Theorems.Thm_TIESharp_lemma_4_5
import Theorems.Thm_TIESharp_consistent_family_locality

set_option autoImplicit false

open MeasureTheory

theorem solution (n : ℕ) (hn : 2 ≤ n) (F : TIESharp.Family n) (R : ℝ)
    (hF : TIESharp.IsFeasible F) (hT : TIESharp.IsTIE F) (hR : TIESharp.IsRApprox F R) :
    ∃ g : Fin n → (Fin n → ℝ) → ℝ,
      (∀ i, Measurable (g i)) ∧
      (∀ i (c : Fin n → ℝ), (∀ a, 0 < c a) → g i c ∈ Set.Icc 0 1) ∧
      ∃ yStar : (m : ℕ) → (Fin n → Fin m → ℝ) → (Fin m → Fin n) → ℝ,
        (∀ (m : ℕ) (A : Fin m → Fin n), Measurable (fun t => yStar m t A)) ∧
        ∀ m : ℕ, 1 ≤ m →
          (∀ᵐ t ∂(volume.restrict {t : Fin n → Fin m → ℝ | ∀ i j, 0 < t i j}),
            (∀ A, 0 ≤ yStar m t A) ∧ ∑ A, yStar m t A = 1 ∧
            (∀ i j, ∑ A ∈ Finset.univ.filter (fun A : Fin m → Fin n => A j = i), yStar m t A
              = g i (fun a => t a j)) ∧
            ∑ A, yStar m t A * MatousekLP.Scheduling.makespan (Matrix.of t) A ≤ R * TIESharp.opt t) ∧
          ∀ (σ : Equiv.Perm (Fin n)) (π : Equiv.Perm (Fin m)),
            ∀ᵐ t ∂(volume.restrict {t : Fin n → Fin m → ℝ | ∀ i j, 0 < t i j}),
              ∀ A : Fin m → Fin n,
                yStar m (fun i j => t (σ.symm i) (π.symm j)) (σ ∘ A ∘ π.symm) = yStar m t A := by
  obtain ⟨F', hF', hT', hR', hcon'⟩ := TIESharp.lemma_4_2 n hn F R hF hT hR
  exact TIESharp.consistent_family_locality n hn R F' hF' hT' hR' hcon'
