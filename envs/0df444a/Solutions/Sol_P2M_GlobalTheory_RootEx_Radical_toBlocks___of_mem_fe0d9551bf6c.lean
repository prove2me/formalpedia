-- Prove2me | solution 1 for P2M_GlobalTheory_RootEx_Radical_toBlocks___of_mem_fe0d9551bf6c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:09.145194+00:00
-- url     : https://prove2.me/submissions/a01a4917-86ed-45aa-bcac-08f3e3318dc2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Theorems.Thm_GlobalTheory_RootEx_Radical_mem_N_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Radical
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.RootEx.Radical
theorem _root_.solution {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) :
    g.val.toBlocks₁₁ = 1 := by
  rw [mem_N_iff] at hg
  ext r s
  simp only [Matrix.toBlocks₁₁, Matrix.of_apply]
  rw [hg _ _ (by simp [lev])]
  simp [Matrix.one_apply]
end GlobalTheory.RootEx.Radical
