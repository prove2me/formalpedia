-- Prove2me | solution 1 for PNormRegLib.step_eq_exec
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-15T08:11:48.936168+00:00
-- url     : https://prove2.me/submissions/24eace6a-cbfc-4797-92ec-8a65131b54e8

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec

open PNormReg PNormRegLib SmaleNinth

namespace PNormRegLibStepAux

lemma RAMStep_eq {R : RAMProgram} {s : RAMConfig} {i : RAMInstr} (h : R[s.pc]? = some i) :
    RAMStep R s = coreExec i s := by
  simp only [RAMStep, h]
  cases i <;> rfl

lemma core_get {P : Program} {pc : ℕ} {i : RAMInstr} (h : P[pc]? = some (.core i)) :
    (coreProgram P)[pc]? = some i := by
  simp [coreProgram, List.getElem?_map, h]

end PNormRegLibStepAux

open PNormRegLibStepAux in
theorem solution (P : Program) (ω : ℕ → Bool) (s : State) (ins : Instr)
    (hh : s.halted = false) (h : P[s.core.pc]? = some ins) : step P ω s = exec ω ins s := by
  cases ins with
  | core i => simp [step, exec, hh, h, RAMStep_eq (core_get h)]
  | _ => simp [step, exec, hh, h]
