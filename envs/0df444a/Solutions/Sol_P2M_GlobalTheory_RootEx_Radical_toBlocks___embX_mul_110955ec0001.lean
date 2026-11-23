-- Prove2me | solution 1 for P2M_GlobalTheory_RootEx_Radical_toBlocks___embX_mul_110955ec0001
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:02.844644+00:00
-- url     : https://prove2.me/submissions/6e3837da-5244-43fc-b460-c1d4b63890c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Theorems.Thm_GlobalTheory_RootEx_Radical_embX_val
import Theorems.Thm_P2M_GlobalTheory_RootEx_Radical_toBlocks___of_mem_fe0d9551bf6c

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
theorem _root_.solution (x : GL n k) {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) :
    (embX c x * g).val.toBlocks₁₁ = x.val := by
  rw [Units.val_mul, embX_val]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks g.val]
  simp [fromBlocks_multiply, toBlocks₁₁_of_mem hg]
end GlobalTheory.RootEx.Radical
