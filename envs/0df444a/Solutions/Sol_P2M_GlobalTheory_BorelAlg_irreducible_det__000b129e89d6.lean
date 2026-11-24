-- Prove2me | solution 1 for P2M_GlobalTheory_BorelAlg_irreducible_det__000b129e89d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:09:42.657905+00:00
-- url     : https://prove2.me/submissions/75489a40-5d0d-4ee5-aa7e-3e27317e7167

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero
import Theorems.Thm_GlobalTheory_RowDet_irreducible_det


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
theorem _root_.solution {R σ : Type*} [CommRing R] [IsDomain R] {k : ℕ} (hk : k ≠ 0)
    (e : Fin k × Fin k → σ) (he : Function.Injective e) :
    Irreducible (Matrix.of fun i j : Fin k => (X (e (i, j)) : MvPolynomial σ R)).det := by
  cases k with
  | zero => exact absurd rfl hk
  | succ n => exact RowDet.irreducible_det n e he
end GlobalTheory.BorelAlg
