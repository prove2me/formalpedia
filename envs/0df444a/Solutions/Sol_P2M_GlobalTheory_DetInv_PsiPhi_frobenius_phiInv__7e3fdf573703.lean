-- Prove2me | solution 1 for P2M_GlobalTheory_DetInv_PsiPhi_frobenius_phiInv__7e3fdf573703
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:31:27.526964+00:00
-- url     : https://prove2.me/submissions/fd6c35e6-e097-4b0f-9ddf-3b271fc8e9c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IotaScalarOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusOfPadic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
open GlobalTheory GlobalTheory.DetInv GlobalTheory.DetInv.PsiPhi
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]
namespace GlobalTheory.DetInv.PsiPhi
theorem _root_.solution (a : Ainf p O) : WittVector.frobenius (phiInv p O a) = a := by
  rw [WittVector.frobenius_eq_map_frobenius]
  ext n
  simp only [phiInv, WittVector.map_coeff]
  exact frobenius_apply_frobeniusEquiv_symm (PreTilt O p) p _
end GlobalTheory.DetInv.PsiPhi
