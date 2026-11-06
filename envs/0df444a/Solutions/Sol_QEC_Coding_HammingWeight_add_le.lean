-- Prove2me | solution 1 for QEC.Coding.HammingWeight_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:07:08.936845+00:00
-- url     : https://prove2.me/submissions/e8493116-10bd-4934-94ea-ad52fc1e0c02

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
import Theorems.Thm_QEC_Coding_hammingSupport_add_subset_union

set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
namespace QEC.Coding
theorem _root_.solution {F : Type u} {ι : Type v}
    [AddGroup F] [DecidableEq F] [Fintype ι] (x y : Word F ι) :
    HammingWeight (x + y) ≤ HammingWeight x + HammingWeight y := by
  classical
  calc
    HammingWeight (x + y) = (hammingSupport (x + y)).card :=
      HammingWeight_eq_card_hammingSupport (x + y)
    _ ≤ (hammingSupport x ∪ hammingSupport y).card :=
      Finset.card_le_card (hammingSupport_add_subset_union x y)
    _ ≤ (hammingSupport x).card + (hammingSupport y).card :=
      Finset.card_union_le (hammingSupport x) (hammingSupport y)
    _ = HammingWeight x + HammingWeight y := by
      rw [← HammingWeight_eq_card_hammingSupport x, ← HammingWeight_eq_card_hammingSupport y]
end QEC.Coding
