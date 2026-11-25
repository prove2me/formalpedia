-- Prove2me | solution 1 for P2M_GlobalTheory_UnitarySplit_cT_add__9947e56985ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:34:30.304911+00:00
-- url     : https://prove2.me/submissions/4693f4ed-976e-44de-b33d-b00ba7ea1439

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
theorem _root_.solution (c : A →+* A) (M N : Matrix (Fin n) (Fin n) A) :
    cT c (M + N) = cT c M + cT c N := by
  ext i j; simp [cT]
end GlobalTheory.UnitarySplit
