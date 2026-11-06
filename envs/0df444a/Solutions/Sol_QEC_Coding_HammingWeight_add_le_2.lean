-- Prove2me | solution 2 for QEC.Coding.HammingWeight_add_le
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:15:23.538749+00:00
-- url     : https://prove2.me/submissions/e593778b-0cff-451e-b2dc-43f62f002c3a

-- ID: b8d80877-3af4-4ee2-87d3-888914692649 | NAME: QEC.Coding.HammingWeight_add_le | 未本地编译验证
import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x

theorem solution {F : Type u} {ι : Type v}
    [AddGroup F] [DecidableEq F] [Fintype ι] (x y : Word F ι) :
    HammingWeight (x + y) ≤ HammingWeight x + HammingWeight y := by
  letI := Classical.decEq ι
  unfold HammingWeight
  calc
    (hammingSupport (x + y)).card ≤ (hammingSupport x ∪ hammingSupport y).card := by
      apply Finset.card_le_card
      intro i hi
      simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union] at hi ⊢
      by_cases hx : x i = 0
      · right
        intro hy
        apply hi
        simp [Pi.add_apply, hx, hy]
      · exact Or.inl hx
    _ ≤ (hammingSupport x).card + (hammingSupport y).card := Finset.card_union_le _ _
