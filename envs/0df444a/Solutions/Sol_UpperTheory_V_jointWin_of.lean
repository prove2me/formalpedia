-- Prove2me | solution 1 for UpperTheory.V.jointWin_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:40:48.685226+00:00
-- url     : https://prove2.me/submissions/fdfdcd27-935a-48c7-84f3-9c228758a420

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_LengthEqAddEigen
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_StmtFields
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PrimeSetBoundDataOfPrimitiveChar
import Theorems.Thm_UpperTheory_V_ThmBab_a
import Theorems.Thm_UpperTheory_V_ThmBab_b
import Theorems.Thm_UpperTheory_V_primeSetBoundData_of_primitiveChar
import Theorems.Thm_UpperTheory_V_BConst_J_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open UpperTheory UpperTheory.V
open Formalism.HC UpperTheory.Top
namespace UpperTheory.V
theorem _root_.solution {K : BConst} {Ct : ℝ} (hC : 0 < Ct) (hB : ThmBab K Ct) (hV : ThmHV K Ct) : JointWin Ct := by
  intro ψ eps A1 h0 h1 e t ha
  obtain ⟨X0, H⟩ := hB (AbF.ofChar ψ) (Bchi ψ) (Lchi ψ) (primeSetBoundData_of_primitiveChar ψ) eps A1 h0 h1
  obtain ⟨C, r₁, r₂, -, -, H'⟩ := hV ψ
  obtain ⟨X1, H'⟩ := H' eps A1 h0 h1
  refine ⟨Jchi K Ct eps ψ, C, (([ψ.N, ordC ψ, pK ψ, hStar ψ, pOne ψ, r₁, r₂].sum : ℕ) : ℝ), max X0 X1,
    K.J_pos hC h0 _ _ _, fun X hX q d hp a b c c' hl => ?_⟩
  obtain ⟨Y, hY⟩ := H e t ha X ((le_max_left _ _).trans hX) q d hp hl
  refine ⟨Y, hY.1, fun x u v => ⟨(hY.2 x u v).1,
    H' e t ha X ((le_max_right _ _).trans hX) q d hp a b (fun y hy => ?_) hl Y hY x u v⟩⟩
  have := List.le_sum_of_mem hy
  exact ⟨this.trans_lt (by exact_mod_cast c), this.trans_lt (by exact_mod_cast c')⟩
end UpperTheory.V
