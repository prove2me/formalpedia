-- Prove2me | solution 1 for P2M_GlobalTheory_UnitLemma_Unr_NormVal_val_pow__b9bc6e444f01
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:34:24.162821+00:00
-- url     : https://prove2.me/submissions/08da2e44-f045-46ac-a134-a6315f2909fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralBasisUnramifiedInvolutionExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddValNormUnramifiedInvolutionFieldExtEqMul
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_Unr_NormVal_val_mul__bc11e1e41355
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_Unr_NormVal_val_one__ef0fa3e7b004

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.NormVal
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type} [Field E]
    [Algebra O E] [IsFractionRing O E]
namespace GlobalTheory.UnitLemma.Unr.NormVal
theorem _root_.solution {x : E} (hx : x ≠ 0) (k : ℕ) : val O (x ^ k) = k * val O x := by
  induction k with
  | zero => simp [val_one']
  | succ k ih =>
    rw [pow_succ, val_mul' O (pow_ne_zero _ hx) hx, ih]
    push_cast; ring
end GlobalTheory.UnitLemma.Unr.NormVal
