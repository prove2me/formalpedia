-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TrdegAdjoinLe_proof_6070abacc8b1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:55:24.509955+00:00
-- url     : https://prove2.me/submissions/d7615f58-0538-460e-89aa-a04263ae36e6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTrdegAdjoinLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTrdegAdjoinLe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_trdeg_adjoin_eq_cRk_b84e0c0b014c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Algebra Cardinal Set AlgebraicIndependent
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace TrdegAdjoinLe
theorem _root_.solution : TrdegAdjoinLe.Statement := by
  intro K Ω _ _ _ s ι _ t ι' w hw
  set M := AlgebraicIndependent.matroid K Ω
  rw [trdeg_adjoin_eq_cRk, trdeg_adjoin_eq_cRk]
  have hcl : range w ⊆ M.closure (s ∪ range t) := by
    rintro _ ⟨i, rfl⟩
    rw [matroid_closure_eq]
    exact hw i
  calc M.cRk (range w) ≤ M.cRk (M.closure (s ∪ range t)) := M.cRk_le_of_subset hcl
    _ = M.cRk (s ∪ range t) := M.cRk_closure _
    _ ≤ M.cRk (s ∩ range t) + M.cRk (s ∪ range t) := le_add_self
    _ ≤ M.cRk s + M.cRk (range t) := M.cRk_inter_add_cRk_union_le s (range t)
    _ ≤ M.cRk s + #(range t) := by gcongr; exact M.cRk_le_cardinalMk _
    _ ≤ M.cRk s + #ι := by gcongr; exact mk_range_le
    _ = M.cRk s + Fintype.card ι := by rw [mk_fintype]
end TrdegAdjoinLe
end GroundTheory.Heights₂.Heights
