-- Prove2me | solution 1 for PNormRegLib.exists_usesBelow
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-15T08:38:43.363668+00:00
-- url     : https://prove2.me/submissions/75491b60-f373-4424-9ab4-6b2173bdbd01

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Reloc

open PNormReg PNormRegLib SmaleNinth

namespace PNormRegLibUsesAux

/-- The sum of all index arguments of an instruction. -/
def idxSum : Instr → ℕ
  | .core (.const d _) => d
  | .core (.add d i j) | .core (.sub d i j) | .core (.mul d i j) | .core (.div d i j) => d + i + j
  | .core (.load d q) => d + q
  | .core (.store q i) => q + i
  | .core (.pset q _) => q
  | .core (.pcopy q q') => q + q'
  | .core (.pinc q) | .core (.pdec q) => q
  | .core (.jle i _) => i
  | .core (.pjle q q' _) => q + q'
  | .core .accept | .core .reject => 0
  | .pointerAdd d a b | .pointerSub d a b => d + a + b
  | .integerLoad d a => d + a
  | .integerStore a b => a + b
  | .pointerReal d a => d + a
  | .sqrt d a => d + a
  | .rpow d a b => d + a + b
  | .coin d => d
  | .halt => 0

lemma instrOK_of_le {nR nQ : ℕ} (ins : Instr) (h1 : idxSum ins < nR) (h2 : idxSum ins < nQ) :
    InstrOK nR nQ ins := by
  cases ins with
  | core i => cases i <;> simp only [InstrOK, idxSum] at * <;> omega
  | _ => simp only [InstrOK, idxSum] at * <;> omega

end PNormRegLibUsesAux

open PNormRegLibUsesAux in
theorem solution (P : PNormReg.Program) : ∃ n : ℕ, UsesBelow P n n := by
  induction P with
  | nil => exact ⟨0, fun _ h => by simp at h⟩
  | cons a P ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + idxSum a + 1, fun ins h => ?_⟩
    rcases List.mem_cons.mp h with rfl | h
    · exact instrOK_of_le _ (by omega) (by omega)
    · have := hn ins h
      cases ins with
      | core i => cases i <;> simp only [InstrOK] at * <;> omega
      | _ => simp only [InstrOK] at * <;> omega
