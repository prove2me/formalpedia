-- Prove2me | solution 1 for ResourceScheduling.Graph.word_program_emitter
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T13:24:54.193822+00:00
-- url     : https://prove2.me/submissions/07055a64-825d-4e13-a46c-b3f61faf70d8

import Theorems.Thm_ResourceScheduling_Graph_word_non_edges

set_option autoImplicit false
open ResourceScheduling.Graph

/-- The list program emits precisely the original unary encoding of the constructed instance. -/
theorem solution (t : ℕ) (bits : List Letter) (G : SimpleGraph (Fin (3 * t)))
    [DecidableRel G.Adj]
    (h : ∀ i j : Fin (3 * t), G.Adj i j ↔
      bits.getD (i.val * (3 * t) + j.val) Letter.sep = Letter.one) :
    emitQ2Word t bits = encQ2 (![2, 1], construct G t) := by
  have hp := word_non_edges (3 * t) bits G h
  let row (p : Fin (3 * t) × Fin (3 * t)) :=
    (List.finRange (3 * t)).flatMap fun i => unary (if i = p.1 ∨ i = p.2 then 1 else 0)
  have hr := congrArg (fun ps : List (Fin (3 * t) × Fin (3 * t)) => ps.flatMap row)
    (List.map_get_finRange (nonEdgeList G))
  simp only [List.flatMap_map] at hr
  have hrow (p : Fin (3 * t) × Fin (3 * t)) :
      (List.range (3 * t)).flatMap (fun i => unary (if i = p.1.val ∨ i = p.2.val then 1 else 0)) = row p := by
    rw [← List.map_coe_finRange_eq_range (n := 3 * t)]
    simp only [List.flatMap_map, Function.comp_def, row]
    congr 1
    funext i
    simp only [Fin.val_inj]
  simp only [emitQ2Word, hp, List.length_map, List.flatMap_map, encQ2, construct,
    ResDot11Data.enc, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, PNat.val_ofNat]
  rw [hr]
  simp only [hrow, List.append_assoc]

#print axioms solution
