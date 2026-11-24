-- Prove2me | solution 1 for P2M_GlobalTheory_BorelAlg_minor_isRelPrime__ca4173270435
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:22:02.652624+00:00
-- url     : https://prove2.me/submissions/f78db8ff-0df2-4ec2-8ad0-8141cad93611

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero
import Theorems.Thm_GlobalTheory_RowDet_det_updateRow_single
import Theorems.Thm_GlobalTheory_RowDet_minor_isRelPrime


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.BorelAlg
namespace GlobalTheory.BorelAlg
theorem _root_.solution {R σ : Type*} [CommRing R] [IsDomain R] {k : ℕ}
    (e : Fin k × Fin k → σ) (he : Function.Injective e) (l : Fin k) (hl : ∀ i, i ≤ l) :
    ((Matrix.of fun i j : Fin k => (X (e (i, j)) : MvPolynomial σ R)).updateRow l
      (Pi.single l 1)).det ≠ 0 ∧
    IsRelPrime ((Matrix.of fun i j : Fin k => (X (e (i, j)) : MvPolynomial σ R)).updateRow l
      (Pi.single l 1)).det
      (Matrix.of fun i j : Fin k => (X (e (i, j)) : MvPolynomial σ R)).det := by
  cases k with
  | zero => exact l.elim0
  | succ n =>
    obtain rfl : l = Fin.last n := le_antisymm (Fin.le_last _) (hl _)
    rw [RowDet.det_updateRow_single]
    exact RowDet.minor_isRelPrime e he
end GlobalTheory.BorelAlg
