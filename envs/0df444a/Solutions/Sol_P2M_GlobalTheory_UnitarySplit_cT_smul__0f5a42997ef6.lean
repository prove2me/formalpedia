-- Prove2me | solution 1 for P2M_GlobalTheory_UnitarySplit_cT_smul__0f5a42997ef6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:34:36.781453+00:00
-- url     : https://prove2.me/submissions/6ec414f8-4b41-4f0b-945e-0e0293f1c012

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
theorem _root_.solution (c : A →+* A) (a : A) (M : Matrix (Fin n) (Fin n) A) :
    cT c (a • M) = c a • cT c M := by
  ext i j; simp [cT]
end GlobalTheory.UnitarySplit
