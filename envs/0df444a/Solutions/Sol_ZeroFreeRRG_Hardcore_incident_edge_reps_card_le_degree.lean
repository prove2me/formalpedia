-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.incident_edge_reps_card_le_degree
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:10:51.272443+00:00
-- url     : https://prove2.me/submissions/0a02f895-bce9-4425-a4b0-2b7b039d7462

import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (d n : ℕ) (M : Matching n d) (v : Fin n) :
    ((edgeReps M).filter (fun x => x.1 = v ∨ (M.1 x).1 = v)).card ≤ d := by
  classical
  let E := (edgeReps M).filter (fun x => x.1 = v ∨ (M.1 x).1 = v)
  let f : (Fin n × Fin d) → Fin d := fun x => if x.1=v then x.2 else (M.1 x).2
  have hinj : Set.InjOn f E := by
    intro x hx y hy hxy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    have hxrep : halfEdgeCode x < halfEdgeCode (M.1 x) := (Finset.mem_filter.mp hx'.1).2
    have hyrep : halfEdgeCode y < halfEdgeCode (M.1 y) := (Finset.mem_filter.mp hy'.1).2
    by_cases h1 : x.1=v <;> by_cases h2 : y.1=v
    · apply Prod.ext
      · exact h1.trans h2.symm
      · simpa [f,h1,h2] using hxy
    · have hyv : (M.1 y).1 = v := hy'.2.resolve_left h2
      have heq : x = M.1 y := by
        apply Prod.ext
        · exact h1.trans hyv.symm
        · simpa [f,h1,h2] using hxy
      have hMX : M.1 x = y := by rw [heq]; exact M.2.1 y
      rw [heq,M.2.1 y] at hxrep
      omega
    · have hxv : (M.1 x).1 = v := hx'.2.resolve_left h1
      have heq : M.1 x = y := by
        apply Prod.ext
        · exact hxv.trans h2.symm
        · simpa [f,h1,h2] using hxy
      have hMY : M.1 y = x := by rw [← heq]; exact M.2.1 x
      rw [← heq,M.2.1 x] at hyrep
      omega
    · have hxv : (M.1 x).1 = v := hx'.2.resolve_left h1
      have hyv : (M.1 y).1 = v := hy'.2.resolve_left h2
      apply M.1.injective
      apply Prod.ext
      · exact hxv.trans hyv.symm
      · simpa [f,h1,h2] using hxy
  have hh := Finset.card_le_card_of_injOn (s := E) (t := (Finset.univ : Finset (Fin d)))
    f (by intro x hx; simp) hinj
  simpa using hh
