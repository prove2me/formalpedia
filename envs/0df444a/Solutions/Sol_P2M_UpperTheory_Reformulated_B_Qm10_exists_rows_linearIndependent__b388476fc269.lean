-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qm10_exists_rows_linearIndependent__b388476fc269
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:00:20.436618+00:00
-- url     : https://prove2.me/submissions/40c4af2f-4014-4927-b01d-24d0538cb00f

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsRowsLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qm10.exists_rows_linearIndependent
theorem _root_.solution.{u, u_1, u_2} :
    ∀ {K : Type u_1} [inst : Field K] {r : Type u} {c : Type u_2} [Fintype r] [inst_2 : Fintype c]
    (P : Matrix r c K) {k : ℕ}, k ≤ P.rank → ∃ (I : Fin k → r), LinearIndependent K fun (p : Fin k) ↦ P (I p) := by
  intro K _ r c _ _ P k hk
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K P.row
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card (Fin k) ≤ Fintype.card κ := by
    rw [Fintype.card_fin, ← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_row]
    exact hk
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨fun p ↦ a (e p), hli.comp e e.injective⟩
end UpperTheory.Reformulated.B.Qm10.exists_rows_linearIndependent
