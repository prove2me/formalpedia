-- Prove2me | solution 1 for P2M_GlobalTheory_UnitarySplit_cT_cT__65cdfa7a426c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:34:32.855561+00:00
-- url     : https://prove2.me/submissions/9bf7a477-d0fc-49c2-b515-abe6b541aa7b

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitarySupportedEquiv
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG
open GlobalTheory GlobalTheory.UnitarySplit
variable {A : Type} [CommRing A] {n : ℕ}
namespace GlobalTheory.UnitarySplit
theorem _root_.solution (c : A →+* A) (hc : ∀ x, c (c x) = x) (M : Matrix (Fin n) (Fin n) A) :
    cT c (cT c M) = M := by
  ext i j; simp [cT, hc]
end GlobalTheory.UnitarySplit
