-- Prove2me | solution 1 for PositivityTheory.CW.column_moments_of_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:54:34.109535+00:00
-- url     : https://prove2.me/submissions/d888b80c-44d9-47a6-834a-5bcd3ee4b9bc

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_ColumnMomentsOfSymmetric
import Theorems.Thm_PositivityTheory_CW_MatrixActionSingle_act_mul
import Theorems.Thm_PositivityTheory_CW_MatrixActionSingle_act_pow
import Theorems.Thm_PositivityTheory_CW_MatrixActionSingle_adj
import Theorems.Thm_P2M_PositivityTheory_CW_MatrixActionSingle_adj__27900db94784
import Theorems.Thm_PositivityTheory_CW_MatrixActionSingle_act_single
import Theorems.Thm_PositivityTheory_CW_MatrixActionSingle_inner_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open MatrixActionSingle
namespace PositivityTheory.CW
theorem _root_.solution : A7 → ColumnOperatorMoments := by
  intro h7
  unfold ColumnOperatorMoments ForMod
  intro n ε V _ _ E hM v hv e j
  have hu := hM.uni
  have hsa : ∀ y z : PiLp 2 (fun _ : Fin n => V),
      inner ℂ (act (Md ε E * Mm E) y) z = inner ℂ y (act (Md ε E * Mm E) z) := by
    intro y z
    rw [act_mul, act_mul, adj' ε E hu, adj ε E hu]
  have hxn : ‖(PiLp.single 2 e v : PiLp 2 (fun _ : Fin n => V))‖ = 1 := by
    rw [PiLp.norm_single, hv]
  have hn : ‖act (Mm E) (PiLp.single 2 e v : PiLp 2 (fun _ : Fin n => V))‖ ^ 2
      = ∑ a, ‖E a e v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := act_single (Mm E) e a v
    simp only [Mm, Matrix.of_apply] at this
    rw [← this]
    rfl
  have hq : inner ℂ (PiLp.single 2 e v : PiLp 2 (fun _ : Fin n => V))
      (act (Md ε E * Mm E) (PiLp.single 2 e v)) = ((∑ a, ‖E a e v‖ ^ 2 : ℝ) : ℂ) := by
    rw [act_mul, ← adj ε E hu, inner_self_eq_norm_sq_to_K, ← hn]
    norm_cast
  have hre : (inner ℂ (PiLp.single 2 e v : PiLp 2 (fun _ : Fin n => V))
      (act (Md ε E * Mm E) (PiLp.single 2 e v))).re = ∑ a, ‖E a e v‖ ^ 2 := by
    rw [hq, Complex.ofReal_re]
  have key := h7 (PiLp 2 (fun _ : Fin n => V)) (act (Md ε E * Mm E)) hsa
    (PiLp.single 2 e v) hxn (by rw [hre]; positivity) j
  rw [hre, ← act_pow, inner_single, act_single] at key
  exact key
end PositivityTheory.CW
