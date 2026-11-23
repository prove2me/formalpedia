-- Prove2me | solution 1 for TIESharp.theorem_3_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:30:20.51769+00:00
-- url     : https://prove2.me/submissions/89b06713-fbd1-4103-b4c8-3b898ced27e8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TIESharp_IsTIE
import Definitions.Def_TIESharp_opt
import Definitions.Def_TIESharp_IsBSSlotLaw
import Definitions.Def_TIESharp_bsPay
import Theorems.Thm_TIESharp_lemma_5_1
import Theorems.Thm_TIESharp_proposition_5_5
import Theorems.Thm_TIESharp_bsSlotLaw_exists
import Theorems.Thm_TIESharp_bsCol_payment_properties
import Theorems.Thm_TIESharp_makespan_bounds_except_seven
import Theorems.Thm_TIESharp_bsSlotLaw_zero_opt_support

set_option autoImplicit false

open TIESharp

theorem solution (n : ℕ) (hn : 2 ≤ n) :
    (∀ (m : ℕ) (t : Fin n → Fin m → ℝ), Nonneg t → ∃ y, IsBSSlotLaw t y) ∧
    (∀ F : Family n,
      (∀ (m : ℕ) (b : Fin n → Fin m → ℝ), Nonneg b →
        IsBSSlotLaw b (F.alloc m b) ∧ ∀ i, F.pay m b i = ∑ j, bsPay b i j) →
      IsTIE F) ∧
    (∀ (m : ℕ) (t : Fin n → Fin m → ℝ) (i : Fin n) (j : Fin m), Nonneg t →
      MeasureTheory.IntegrableOn (fun u => bsCol (Function.update (fun k => t k j) i u) i)
        (Set.Ioi (t i j))) ∧
    (∀ (m : ℕ) (t : Fin n → Fin m → ℝ) (y : (Fin m → Fin n) → ℝ), Nonneg t → IsBSSlotLaw t y →
      (7 ≤ n → ∑ A, y A * MatousekLP.Scheduling.makespan (Matrix.of t) A
          ≤ ((n : ℝ) + 1) / 2 * opt t) ∧
      (n = 4 → ∑ A, y A * MatousekLP.Scheduling.makespan (Matrix.of t) A ≤ 3 * opt t) ∧
      (n = 5 → ∑ A, y A * MatousekLP.Scheduling.makespan (Matrix.of t) A ≤ 105 / 32 * opt t) ∧
      (n = 6 → ∑ A, y A * MatousekLP.Scheduling.makespan (Matrix.of t) A ≤ 29 / 8 * opt t) ∧
      (opt t = 0 → ∀ A, 0 < y A → MatousekLP.Scheduling.makespan (Matrix.of t) A = 0)) := by
  have hprops : ∀ (m : ℕ) (b : Fin n → Fin m → ℝ) (i : Fin n) (j : Fin m),
      Nonneg b →
        0 ≤ bsCol (fun k => b k j) i ∧
        (∑ k, bsCol (fun k => b k j) k) = 1 ∧
        AntitoneOn (fun s => bsCol (Function.update (fun k => b k j) i s) i) (Set.Ici 0) ∧
        MeasureTheory.IntegrableOn
          (fun u => bsCol (Function.update (fun k => b k j) i u) i) (Set.Ioi 0) ∧
        ∀ s : ℝ, 0 ≤ s → MeasureTheory.IntegrableOn
          (fun u => bsCol (Function.update (fun k => b k j) i u) i) (Set.Ioi s) := by
    intro m b i j hb
    exact bsCol_payment_properties n hn (fun k => b k j) (fun k => hb k j) i
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m t ht
    exact bsSlotLaw_exists n hn m t ht
  · intro F hF
    intro m b i ti bi hb hti hbi
    have hb_bi : Nonneg (Function.update b i bi) := by
      intro a j
      by_cases hai : a = i
      · subst a
        simpa using hbi j
      · simpa [Function.update, hai] using hb a j
    have hb_ti : Nonneg (Function.update b i ti) := by
      intro a j
      by_cases hai : a = i
      · subst a
        simpa using hti j
      · simpa [Function.update, hai] using hb a j
    have hy : ∀ (b : Fin n → Fin m → ℝ), Nonneg b →
        (∀ A, 0 ≤ F.alloc m b A) ∧ ∑ A, F.alloc m b A = 1 ∧
        ∀ i j, ∑ A ∈ Finset.univ.filter (fun A : Fin m → Fin n => A j = i), F.alloc m b A
          = bsCol (fun a => b a j) i := by
      intro b' hb'
      have h := (hF m b' hb').1
      exact ⟨h.1, h.2.1, h.2.2.1⟩
    have hmain := lemma_5_1 n m (fun _j i c => bsCol c i)
      (fun j i c hc => (bsCol_payment_properties n hn c hc i).1)
      (fun j c hc => (bsCol_payment_properties n hn c hc
        (Classical.choice (show Nonempty (Fin n) from ⟨⟨0, by omega⟩⟩))).2.1)
      (fun j i c hc => (bsCol_payment_properties n hn c hc i).2.2.1)
      (fun j i c hc => (bsCol_payment_properties n hn c hc i).2.2.2.1)
      (fun b' => F.alloc m b') hy b i ti bi hb hti hbi
    rw [(hF m (Function.update b i bi) hb_bi).2 i,
      (hF m (Function.update b i ti) hb_ti).2 i]
    simpa only [bsPay, bsProb, marg] using hmain
  · intro m t i j ht
    exact (hprops m t i j ht).2.2.2.2 (t i j) (ht i j)
  · intro m t y ht hy
    have hg := makespan_bounds_except_seven n m hn t ht y hy
    refine ⟨?_, hg.2.1, hg.2.2.1, hg.2.2.2, ?_⟩
    · intro hn7
      by_cases h7 : n = 7
      · subst n
        convert proposition_5_5 m t ht y hy using 1 <;> norm_num
      · apply hg.1
        omega
    · exact fun hopt A hA => bsSlotLaw_zero_opt_support n m hn t ht y hy hopt A hA