-- Prove2me | solution 1 for SteinitzExchange.Duality.neg_conjugate_closure
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:32:13.752987+00:00
-- url     : https://prove2.me/submissions/0f46fb57-8bfd-465c-8e09-31626a7e9758

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_Conjugate

namespace SteinitzExchange.Duality

theorem aux_ncc_iInf_eq {ι : Sort*} (g : ι → ℝ) : ⨅ i, g i = -⨆ i, -g i := by
  rw [iInf, Real.sInf_def, iSup]
  congr 2
  ext x
  simp only [Set.mem_neg, Set.mem_range]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i, by rw [hi, neg_neg]⟩
  · rintro ⟨i, hi⟩; exact ⟨i, by rw [← hi, neg_neg]⟩

theorem aux_ncc_pairing_neg {V : Type*} [Fintype V] (p b : V → ℝ) :
    pairing (-p) b = -pairing p b := by
  simp [pairing, Finset.sum_neg_distrib]

theorem aux_ncc_part1 {V : Type*} [Fintype V] (B : Finset (V → ℤ)) (f : (V → ℤ) → ℝ)
    (p : V → ℝ) : concaveConj B (fun x => -f x) p = -convexConj B f (-p) := by
  unfold concaveConj convexConj
  rw [aux_ncc_iInf_eq]
  congr 2
  funext x
  rw [aux_ncc_pairing_neg]
  ring

end SteinitzExchange.Duality

open SteinitzExchange.Duality

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : B.Nonempty) (f : (V → ℤ) → ℝ) :
    (∀ p : V → ℝ, concaveConj B (fun x => -f x) p = -convexConj B f (-p)) ∧
    (∀ b ∈ hull B, concaveClosure B (fun x => -f x) b = -convexClosure B f b) := by
  refine ⟨fun p => aux_ncc_part1 B f p, fun b _ => ?_⟩
  unfold concaveClosure convexClosure
  rw [aux_ncc_iInf_eq, ← (Equiv.neg (V → ℝ)).iSup_comp]
  congr 2
  funext q
  simp only [Equiv.neg_apply]
  rw [aux_ncc_part1, aux_ncc_pairing_neg]
  rw [neg_neg]
  ring
