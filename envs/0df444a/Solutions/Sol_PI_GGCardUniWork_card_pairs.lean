-- Prove2me | solution 1 for PI.GGCardUniWork.card_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:40:58.290603+00:00
-- url     : https://prove2.me/submissions/33032207-b159-4dff-bd22-9a9eb488142f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCardinality_UniMatUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GGCardUniWork
open Finset Matrix Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ}
namespace PI.GGCardUniWork
theorem _root_.solution (k : ℕ) : Fintype.card (Pairs k) = k * (k - 1) / 2 := by
  have hI : ∀ j : Fin k, (∑ i : Fin k, if i < j then 1 else 0) = (j : ℕ) := fun j => by
    rw [← Finset.card_filter]
    rw [show (Finset.univ.filter fun i : Fin k => i < j) = Finset.Iio j by ext i; simp]
    exact Fin.card_Iio j
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]
  simp only [hI]
  have h3 : ∑ j : Fin k, (j : ℕ) = ∑ j ∈ Finset.range k, j := Fin.sum_univ_eq_sum_range (fun i => i) k
  rw [h3, Finset.sum_range_id]
end PI.GGCardUniWork
