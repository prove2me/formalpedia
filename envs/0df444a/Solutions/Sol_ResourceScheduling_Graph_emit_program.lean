-- Prove2me | solution 1 for ResourceScheduling.Graph.emit_program
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T16:02:52.812589+00:00
-- url     : https://prove2.me/submissions/6e3c1b60-3ae8-4d9b-a4f5-044921c1cbff

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
import Theorems.Thm_ResourceScheduling_Graph_emit_header
import Theorems.Thm_ResourceScheduling_Graph_emit_rows
import Theorems.Thm_ResourceScheduling_Graph_block_laws
import Theorems.Thm_ResourceScheduling_Graph_ram_safe_laws
import Theorems.Thm_ResourceScheduling_Graph_ram_footprint

set_option autoImplicit false
open ResourceScheduling.Graph GraphReg GraphProgram

theorem solution (B : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s)
    (hn : s.val n = 3 * s.val t) (hc : s.val count = (wordNonEdges (s.val n) s.word).length)
    (hB : s.val n * s.val n + s.val n ≤ B) (hpos : 2 ≤ B) :
    RAMSafe emit B s ∧ (emit.eval s).out = (emitQ2Word (s.val t) s.word).reverse ++ s.out := by
  let hd : List Code := [.zero num, .inc num, .inc num, .emit num,
    .zero num, .inc num, .emit num, .emit n, .emit count]
  let x := (block hd).eval s
  obtain ⟨hh,he⟩ := emit_header B s hs hpos
  have hxn : x.val n = s.val n := by simp only [x, hd, he, RAMState.set, Function.update_of_ne (by decide : n ≠ num)]
  have hxt : x.val t = s.val t := by simp only [x, hd, he, RAMState.set, Function.update_of_ne (by decide : t ≠ num)]
  have hxw : x.word = s.word := by simp only [x, hd, he, RAMState.set]
  have hxo : x.out = (unary 2 ++ unary 1 ++ unary (s.val n) ++ unary (s.val count)).reverse ++ s.out := by
    simp only [x, hd, he]
  obtain ⟨hr,ho⟩ := emit_rows B (s.val n) x hh.2 hxn hB (by omega)
  let y := emitRows.eval x
  have hyt : y.val t = s.val t := (ram_footprint emitRows t (by rfl) x).trans hxt
  have hlast := (ram_safe_laws (.emit t) .skip n B y).2.1 ⟨hr.2,hr.2⟩ ⟨hr.2,hr.2⟩
  have htail : RAMSafe (block [emitRows, .emit t]) B x :=
    (ram_safe_laws emitRows ((RAMCode.emit t).seq .skip) n B x).2.1 hr hlast
  have hsafe := (block_laws hd [emitRows,.emit t] B s).2 hh htail
  refine ⟨hsafe, ?_⟩
  have hev : emit.eval s = (RAMCode.emit t).eval y := by
    simp only [emit, block, hd, x, y, List.foldr_cons, List.foldr_nil, RAMCode.eval]
  rw [hev]
  change Letter.sep :: (List.replicate (y.val t) Letter.one ++ y.out) = _
  rw [hyt, show y.out = _ from ho, hxw, hxo, hc, hn]
  simp [emitQ2Word, unary, List.reverse_append, List.append_assoc]

#print axioms solution
