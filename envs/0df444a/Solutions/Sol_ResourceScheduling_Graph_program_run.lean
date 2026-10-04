-- Prove2me | solution 1 for ResourceScheduling.Graph.program_run
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T16:02:53.651875+00:00
-- url     : https://prove2.me/submissions/9762d371-c0e3-46c6-b5a4-d7cd8b65e6ba

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMFields
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
import Theorems.Thm_ResourceScheduling_Graph_prepare_eval
import Theorems.Thm_ResourceScheduling_Graph_prepare_safe
import Theorems.Thm_ResourceScheduling_Graph_validate_program
import Theorems.Thm_ResourceScheduling_Graph_count_program
import Theorems.Thm_ResourceScheduling_Graph_emit_program
import Theorems.Thm_ResourceScheduling_Graph_ram_safe_laws
import Theorems.Thm_ResourceScheduling_Graph_ram_footprint
import Theorems.Thm_ResourceScheduling_Graph_ram_field_frame
import Theorems.Thm_ResourceScheduling_Graph_split_ones
import Theorems.Thm_ResourceScheduling_Graph_word_flag

set_option autoImplicit false
open ResourceScheduling.Graph GraphReg GraphProgram

theorem solution (B L : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s)
    (hL : s.word.length ≤ L) (hB : 9 * L * L + 3 * L + 2 ≤ B) :
    RAMSafe program B s ∧ (program.eval s).out = (wordProgram s.word).reverse ++ s.out := by
  let T := (splitOnes s.word).1
  let bits := (splitOnes s.word).2.tail
  let N := 3 * T
  have ht : T ≤ L := by have := (split_ones s.word).2.2.1; dsimp [T]; omega
  have hN : N * N + N + 1 ≤ B := by
    have := Nat.mul_le_mul ht ht
    dsimp [N]; nlinarith
  generalize hx : prepare.eval s = x
  generalize hy : validate.eval x = y
  have hp := prepare_safe B L s hs hL (by omega)
  obtain ⟨hxt,hxn,hxw,hxo,hxg⟩ := prepare_eval s
  rw [hx] at hxt hxn hxw hxo hxg
  have hpx : RAMBound B x := by simpa only [hx] using hp.2
  obtain ⟨hv,hvg⟩ := validate_program B N x hpx hxn (by omega) (by omega)
  rw [hy] at hvg
  have hpy : RAMBound B y := by simpa only [hy] using hv.2
  have hyn : y.val n = N := by simpa only [hy] using (ram_footprint validate n (by rfl) x).trans hxn
  have hyt : y.val t = T := by simpa only [hy] using (ram_footprint validate t (by rfl) x).trans hxt
  have hyw : y.word = bits := by simpa [hy, RAMState.field] using (ram_field_frame validate true (by rfl) x).trans hxw
  have hyo : y.out = s.out := by simpa [hy, RAMState.field] using (ram_field_frame validate false (by rfl) x).trans hxo
  generalize hz : countEdges.eval y = z
  obtain ⟨hc,hzc⟩ := count_program B N y hpy hyn hN
  rw [hz] at hzc
  have hpz : RAMBound B z := by simpa only [hz] using hc.2
  have hzn : z.val n = N := by simpa only [hz] using (ram_footprint countEdges n (by rfl) y).trans hyn
  have hzt : z.val t = T := by simpa only [hz] using (ram_footprint countEdges t (by rfl) y).trans hyt
  have hzw : z.word = bits := by simpa [hz, RAMState.field] using (ram_field_frame countEdges true (by rfl) y).trans hyw
  have hzo : z.out = s.out := by simpa [hz, RAMState.field] using (ram_field_frame countEdges false (by rfl) y).trans hyo
  obtain ⟨he,heo⟩ := emit_program B z hpz (by rw [hzn,hzt])
    (by simpa only [hzn,hzw,hyw] using hzc) (by rw [hzn]; omega) (by omega)
  let q := block [countEdges,emit]
  have hpost := (ram_safe_laws emit .skip n B z).2.1 he ⟨he.2,he.2⟩
  have hq : RAMSafe q B y := (ram_safe_laws countEdges (emit.seq .skip) n B y).2.1 hc
    (by simpa only [hz] using hpost)
  have hbr : RAMSafe (.branch good q .skip) B y :=
    (ram_safe_laws q .skip good B y).2.2 hq ⟨hpy,hpy⟩
  have htail := (ram_safe_laws (.branch good q .skip) .skip n B y).2.1 hbr ⟨hbr.2,hbr.2⟩
  have hmid := (ram_safe_laws validate ((RAMCode.branch good q .skip).seq .skip) n B x).2.1 hv
    (by simpa only [hy] using htail)
  have hall := (ram_safe_laws prepare (validate.seq ((RAMCode.branch good q .skip).seq .skip)) n B s).2.1 hp
    (by simpa only [hx] using hmid)
  have hw : wordProgram s.word = if 0 < y.val good then emitQ2Word T bits else [] :=
    word_flag s.word x.word N (x.val good) (y.val good) rfl hxw
      (hxg.trans (congrArg (fun b => if (splitOnes s.word).2 ≠ [] ∧ b.length = N * N then 1 else 0) hxw.symm)) hvg
  refine ⟨hall, ?_⟩
  have hev : program.eval s = if 0 < y.val good then emit.eval z else y := by
    change (if 0 < (validate.eval (prepare.eval s)).val good then
      emit.eval (countEdges.eval (validate.eval (prepare.eval s))) else validate.eval (prepare.eval s)) = _
    rw [hx, hy, hz]
  have heout : (emit.eval z).out = (emitQ2Word T bits).reverse ++ s.out :=
    heo.trans (by rw [hzt, hzw, hzo])
  rw [hev, hw]
  by_cases hgood : 0 < y.val good
  · simpa only [hgood, if_true] using heout
  · simp [hgood, hyo]

#print axioms solution
